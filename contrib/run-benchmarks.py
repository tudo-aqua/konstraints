#!/usr/bin/env python3
#  SPDX-License-Identifier: Apache-2.0
#
#  Copyright 2023-2025 The Konstraints Authors
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.

import json
import logging
import re
import subprocess
import tarfile
from concurrent.futures import Executor, ThreadPoolExecutor
from dataclasses import dataclass
from logging import INFO, error, info, warning
from multiprocessing import cpu_count
from pathlib import Path
from subprocess import PIPE, STDOUT, TimeoutExpired
from sys import argv
from tarfile import TarFile
from tempfile import NamedTemporaryFile
from threading import BoundedSemaphore
from time import time

from zstandard import ZstdDecompressor

_decompressor = ZstdDecompressor()


class BoundedThreadPoolExecutor(ThreadPoolExecutor):
    def __init__(
        self,
        max_tasks=None,
        max_workers=None,
        thread_name_prefix="",
        initializer=None,
        initargs=(),
    ):
        super().__init__(
            max_workers=max_workers,
            thread_name_prefix=thread_name_prefix,
            initializer=initializer,
            initargs=initargs,
        )

        if max_tasks is None:
            max_tasks = self._max_workers * 2

        self._semaphore = BoundedSemaphore(max_tasks)

    def submit(self, function, *args, **kwargs):
        self._semaphore.acquire()

        future = super().submit(function, *args, **kwargs)
        future.add_done_callback(lambda _: self._semaphore.release())

        return future


@dataclass
class SolverConfig:
    solver: str
    timeout_sec: int


def main():
    if len(argv) != 5:
        error(f"syntax: {argv[0]} SOLVER TIMEOUT JSON TAR_ROOT")
        exit(1)

    solver, timeout, json_file, tar_root = argv[1:]
    conf = SolverConfig(solver, int(timeout))

    json_path = Path(json_file)
    if json_path.exists():
        with json_path.open() as json_data:
            info(f'Extending existing database file "{json_path}"…')
            data = json.load(json_data)
    else:
        info(f"Creating new database file…")
        data = {}

    parallel_tasks = max(1, cpu_count() - 2)
    info(f"Using up to {parallel_tasks} solver threads.")
    with BoundedThreadPoolExecutor(
        max_workers=parallel_tasks, max_tasks=parallel_tasks * 3
    ) as exc:
        handle_tree(Path(tar_root), data, conf, exc)

    with json_path.open("w") as json_data:
        info(f'Writing database file "{json_path}"…')
        json.dump(data, json_data)


def handle_tree(tar_root: Path, data, conf: SolverConfig, exc: Executor):
    for category in tar_root.iterdir():
        info(f'Reading category "{category.name}"…')

        for set_archive in category.glob("*.tar.zst"):
            info(f'Reading archive file "{set_archive.name}"…')

            with set_archive.open("rb") as file, _decompressor.stream_reader(
                file
            ) as zstd, tarfile.open(mode="r|", fileobj=zstd) as tar:
                handle_archive(tar, data, conf, exc)


def handle_archive(tar: TarFile, data, conf: SolverConfig, exc: Executor):
    for entry in tar:
        if not entry.isfile() or not entry.name.endswith(".smt2"):
            continue

        info(f'Enqueuing SMT file "{entry.name}"…')
        smt = tar.extractfile(entry).read()
        future = exc.submit(handle_smt, smt, conf)

        def callback(f):
            if result := f.result() is not None:
                file_data = data
                for component in entry.name.split("/"):
                    if component:
                        file_data = file_data.setdefault(component, {})
                file_data.setdefault("speeds", {})[conf.solver] = result
                file_data["size"] = entry.size

        future.add_done_callback(callback)


_status = re.compile(r"\( *set-info +:status +([a-z]+) *\)")


def handle_smt(smt: bytes, conf: SolverConfig) -> float | None:
    expected_results = []
    for line in smt.decode().splitlines():
        print("> ", line)
        match = _status.search(line)
        if match:
            expected_results.append(match.group(1))

    if "unknown" in expected_results:
        info("Unknown result, not executing.")
        return None
    info(f"Expected result sequence: {expected_results}")

    with NamedTemporaryFile() as smt_file:
        smt_file.write(smt)
        smt_file.flush()

        try:
            info(f"Starting solver.")
            t_start = time()
            result = subprocess.run(
                [conf.solver, smt_file.name],
                timeout=conf.timeout_sec,
                stdout=PIPE,
                stderr=STDOUT,
            )
            time_total = round(time() - t_start, 2)
            info(f"Solver completed normally in {time_total} seconds.")
        except TimeoutExpired:
            warning(f"Solver encountered timeout, not adding to database!")
            return None

    actual_results = []
    for line in result.stdout.decode().splitlines():
        if "unsat" in line:
            actual_results.append("unsat")
        elif "sat" in line:
            actual_results.append("sat")
    if actual_results != expected_results:
        error(
            f"Solver reported incorrect result sequence {actual_results}, not adding to database!"
        )
        return None

    return time_total


if __name__ == "__main__":
    logging.basicConfig(format="[%(levelname)s] %(message)s", level=INFO)
    main()
