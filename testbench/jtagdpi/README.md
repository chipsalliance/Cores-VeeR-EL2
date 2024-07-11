# SPDX-License-Identifier: Apache-2.0
# Copyright 2024 Antmicro <www.antmicro.com>
# 
# # Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# # http://www.apache.org/licenses/LICENSE-2.0 
# # Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

JTAG DPI module for OpenOCD remote_bitbang driver
=================================================

This DPI module provides a "virtual" JTAG connection between a simulated chip
and [OpenOCD](http://openocd.org/). It makes use of the `remote_bitbang` JTAG
driver shipped with OpenOCD, which forwards JTAG requests over TCP to a remote
server. The `jtagdpi` module is instantiated in the hardware simulation to
receive the JTAG requests from OpenOCD and drive the JTAG pins (TCK, TMS, TDI,
etc.) from it.

The `remote_bitbang` protocol is documented in the OpenOCD source tree at
`doc/manual/jtag/drivers/remote_bitbang.txt`, or online at
https://repo.or.cz/openocd.git/blob/HEAD:/doc/manual/jtag/drivers/remote_bitbang.txt
