#!/usr/bin/env bash
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

set -euo pipefail

if [ "${#}" -ne 1 ]; then
	echo "syntax: ${0} ZENODO_DEPOSITION_ID"
	exit 1
fi

curl -s "https://zenodo.org/api/deposit/depositions/${1}/files" |
	jq -r '.[].links.download | select(contains(".tar.zst"))'
