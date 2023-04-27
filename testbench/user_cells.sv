
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This file contains examples of user (technology specific) cells that can
// be used thruought the core

// Clock gate example
module user_clock_gate (
    input  logic CK,
    output logic Q,
    input  logic EN
);

    logic gate;

    initial gate = 0;
    always @(negedge CK)
        gate <= EN;

    assign Q = CK & gate;

endmodule
