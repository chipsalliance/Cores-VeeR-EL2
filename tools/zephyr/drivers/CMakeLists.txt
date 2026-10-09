# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

add_subdirectory(timer)
add_subdirectory_ifdef(CONFIG_SERIAL serial)
