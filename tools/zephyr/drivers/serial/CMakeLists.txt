# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

zephyr_library_amend(${ZEPHYR_CURRENT_MODULE_DIR}/zephyr)
zephyr_library_sources_ifdef(CONFIG_VEER_EL2_TB_SERIAL veer_el2_tb_mbox.c)

zephyr_link_libraries_ifdef(CONFIG_VEER_EL2_TB_EXIT_ON_MAIN_RETURN -Wl,--wrap=main)
