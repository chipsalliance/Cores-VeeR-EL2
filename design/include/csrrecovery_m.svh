assign csr_addr[11] = (!counter[6]&counter[5]&!counter[4]&counter[2]&!counter[1]
    &!counter[0]) | (!counter[7]&!counter[6]&!counter[4]&counter[3]
    &counter[2]&counter[1]&!counter[0]) | (!counter[7]&!counter[6]
    &!counter[4]&counter[3]&counter[2]&!counter[1]&counter[0]) | (
    counter[6]&!counter[5]&!counter[4]&!counter[3]&!counter[2]&!counter[1]
    &counter[0]) | (!counter[6]&counter[5]&!counter[4]&!counter[3]
    &!counter[2]) | (!counter[7]&!counter[6]&!counter[5]&counter[4]
    &!counter[3]) | (!counter[6]&!counter[5]&counter[4]&counter[2]) | (
    !counter[7]&!counter[6]&!counter[5]&!counter[4]&counter[3]&!counter[2]
    &!counter[1]&!counter[0]);

assign csr_addr[10] = (counter[6]&!counter[5]&!counter[4]&!counter[3]&!counter[2]
    &!counter[1]&counter[0]) | (!counter[6]&counter[4]&!counter[3]
    &counter[2]&!counter[1]&counter[0]) | (!counter[7]&!counter[6]
    &!counter[5]&!counter[4]&!counter[1]&!counter[0]) | (!counter[7]
    &!counter[6]&!counter[4]&counter[3]&!counter[2]&counter[1]&!counter[0]) | (
    !counter[6]&!counter[5]&counter[4]&counter[3]&!counter[2]&counter[1]) | (
    !counter[7]&!counter[6]&counter[3]&counter[2]&!counter[1]&!counter[0]) | (
    !counter[7]&!counter[6]&counter[4]&!counter[2]&!counter[1]&counter[0]) | (
    !counter[6]&counter[5]&counter[4]&counter[2]&!counter[0]) | (
    !counter[7]&!counter[6]&!counter[5]&!counter[4]&counter[2]&counter[1]
    &counter[0]) | (!counter[6]&counter[5]&counter[4]&!counter[3]
    &counter[1]) | (!counter[7]&!counter[6]&!counter[5]&!counter[4]
    &!counter[3]) | (!counter[6]&counter[5]&counter[3]&!counter[2]
    &!counter[1]&counter[0]) | (!counter[6]&counter[5]&counter[4]
    &counter[3]&!counter[1]);

assign csr_addr[9]  = 1'b0;

assign csr_addr[8]  = 1'b0;

assign csr_addr[7] = (!counter[5]&counter[4]&!counter[3]) | (counter[5]
    &!counter[4]&!counter[3]&!counter[1]&!counter[0]) | (counter[4]
    &counter[2]&counter[1]&!counter[0]) | (counter[4]&!counter[3]
    &counter[1]) | (!counter[5]&!counter[3]&counter[1]) | (counter[4]
    &!counter[2]&!counter[1]&counter[0]) | (!counter[5]&counter[4]
    &!counter[2]&counter[1]) | (counter[4]&!counter[3]&counter[2]) | (
    counter[7]) | (counter[5]&counter[3]&!counter[1]&counter[0]) | (
    counter[6]&counter[3]) | (counter[5]&counter[4]&counter[3]&!counter[1]) | (
    !counter[4]&!counter[2]&counter[1]&!counter[0]) | (counter[6]
    &counter[5]) | (!counter[5]&!counter[4]&counter[2]&counter[0]) | (
    !counter[5]&!counter[4]&counter[2]&!counter[1]) | (!counter[6]
    &!counter[5]&!counter[3]);

assign csr_addr[6] = (counter[5]&counter[3]&counter[2]&counter[1]&counter[0]) | (
    counter[4]&counter[3]&!counter[2]&!counter[0]) | (counter[5]
    &counter[4]&!counter[3]&counter[0]) | (!counter[7]&!counter[6]
    &!counter[5]&!counter[3]&!counter[2]&counter[0]) | (!counter[7]
    &!counter[6]&!counter[5]&!counter[3]&counter[1]&!counter[0]) | (
    !counter[7]&!counter[6]&!counter[5]&!counter[3]&!counter[1]
    &counter[0]) | (counter[6]&counter[4]&counter[3]) | (!counter[7]
    &!counter[6]&counter[3]&!counter[2]&counter[1]&!counter[0]) | (
    !counter[7]&!counter[6]&counter[3]&!counter[2]&!counter[1]&counter[0]) | (
    counter[4]&!counter[3]&counter[1]) | (!counter[7]&!counter[6]
    &!counter[5]&counter[4]&!counter[2]) | (counter[7]&!counter[4]
    &!counter[3]&!counter[2]&!counter[1]) | (!counter[7]&!counter[6]
    &!counter[5]&!counter[4]&counter[2]&!counter[1]&!counter[0]) | (
    !counter[7]&!counter[6]&!counter[4]&counter[3]&counter[2]&counter[1]
    &counter[0]) | (counter[6]&counter[5]) | (counter[4]&!counter[3]
    &counter[2]);

assign csr_addr[5] = (counter[5]&counter[4]&counter[3]&!counter[1]&counter[0]) | (
    !counter[5]&!counter[4]&counter[2]&counter[1]&counter[0]) | (
    !counter[6]&counter[5]&counter[3]&!counter[2]&!counter[1]&counter[0]) | (
    !counter[6]&counter[5]&!counter[4]&counter[3]&!counter[2]&!counter[0]) | (
    !counter[5]&!counter[4]&counter[3]&!counter[2]&counter[1]) | (
    counter[7]) | (counter[6]&counter[5]&counter[4]&counter[2]) | (
    counter[6]&counter[5]&counter[4]&counter[1]) | (counter[6]&counter[5]
    &counter[4]&counter[3]) | (counter[5]&counter[4]&counter[3]
    &counter[2]&!counter[0]) | (counter[6]&!counter[5]&counter[4]
    &!counter[3]&!counter[2]&!counter[1]) | (!counter[6]&counter[5]
    &!counter[4]&!counter[3]&counter[2]&counter[1]) | (!counter[6]
    &counter[5]&!counter[4]&!counter[3]&counter[2]&counter[0]) | (
    !counter[6]&counter[4]&counter[3]&!counter[2]&!counter[1]&counter[0]) | (
    counter[6]&!counter[5]&!counter[4]&counter[2]) | (counter[6]
    &!counter[5]&!counter[4]&counter[1]) | (!counter[6]&!counter[5]
    &!counter[4]&!counter[3]&!counter[2]&!counter[1]&!counter[0]) | (
    counter[6]&!counter[5]&!counter[4]&counter[3]);

assign csr_addr[4] = (counter[6]&!counter[5]&!counter[4]&counter[0]) | (
    !counter[7]&!counter[4]&counter[3]&!counter[2]&counter[1]&!counter[0]) | (
    counter[5]&!counter[4]&counter[3]&!counter[2]&!counter[1]&counter[0]) | (
    !counter[6]&counter[5]&counter[4]&!counter[3]&counter[2]&!counter[0]) | (
    !counter[6]&counter[5]&counter[4]&!counter[3]&!counter[1]&counter[0]) | (
    !counter[6]&counter[5]&counter[4]&!counter[3]&!counter[2]&counter[1]) | (
    !counter[6]&!counter[5]&counter[4]&counter[3]&counter[2]&!counter[1]
    &!counter[0]) | (!counter[6]&counter[4]&counter[3]&!counter[2]
    &!counter[1]&counter[0]) | (counter[6]&counter[4]&!counter[3]
    &!counter[2]&!counter[1]) | (!counter[7]&!counter[5]&!counter[4]
    &counter[2]&counter[1]&counter[0]) | (counter[5]&!counter[4]
    &counter[3]&counter[2]&!counter[1]&!counter[0]) | (!counter[7]
    &!counter[6]&!counter[5]&!counter[4]&!counter[2]&!counter[1]
    &!counter[0]) | (counter[6]&!counter[4]&counter[2]) | (counter[6]
    &!counter[4]&counter[1]) | (counter[6]&!counter[4]&counter[3]);

assign csr_addr[3] = (!counter[7]&!counter[6]&!counter[5]&!counter[4]&!counter[3]
    &!counter[1]&counter[0]) | (!counter[5]&counter[4]&counter[3]
    &!counter[2]&counter[1]) | (!counter[6]&!counter[5]&counter[4]
    &!counter[3]&counter[1]) | (!counter[5]&counter[3]&!counter[2]
    &counter[1]&!counter[0]) | (!counter[7]&!counter[6]&!counter[5]
    &!counter[3]&!counter[2]&counter[1]) | (counter[7]&!counter[3]
    &!counter[2]&!counter[1]) | (counter[7]&counter[3]&counter[2]) | (
    counter[6]&counter[5]&!counter[3]&!counter[2]&!counter[1]) | (
    counter[7]&counter[3]&counter[1]) | (counter[6]&counter[3]&counter[2]) | (
    !counter[6]&counter[4]&counter[3]&!counter[2]&!counter[1]&counter[0]) | (
    !counter[7]&!counter[6]&!counter[5]&!counter[3]&counter[2]&!counter[1]) | (
    counter[6]&counter[3]&counter[1]) | (counter[6]&counter[4]&!counter[3]
    &!counter[2]&!counter[1]);

assign csr_addr[2] = (!counter[5]&counter[4]&counter[3]&counter[2]&counter[1]
    &counter[0]) | (!counter[6]&counter[5]&!counter[3]&counter[2]
    &!counter[0]) | (counter[5]&!counter[4]&!counter[3]&!counter[2]
    &!counter[1]) | (counter[7]&!counter[2]&!counter[1]) | (counter[7]
    &counter[2]&counter[1]) | (counter[6]&counter[3]&!counter[2]
    &!counter[1]) | (counter[5]&counter[4]&counter[3]&!counter[2]
    &!counter[1]&counter[0]) | (counter[6]&counter[2]&counter[1]) | (
    !counter[6]&!counter[5]&counter[4]&counter[2]&!counter[1]&!counter[0]) | (
    counter[6]&counter[4]&!counter[2]&!counter[1]) | (!counter[6]
    &!counter[5]&counter[4]&counter[3]&!counter[2]&counter[1]) | (
    !counter[6]&counter[5]&counter[4]&!counter[3]&counter[2]) | (
    counter[5]&!counter[4]&!counter[2]&!counter[1]&!counter[0]) | (
    !counter[6]&counter[5]&!counter[4]&counter[1]&counter[0]) | (
    counter[6]&!counter[2]&!counter[1]&!counter[0]) | (!counter[6]
    &counter[5]&!counter[3]&counter[1]&!counter[0]) | (!counter[7]
    &!counter[6]&!counter[4]&!counter[3]&counter[1]&!counter[0]);

assign csr_addr[1] = (!counter[6]&counter[5]&counter[4]&counter[2]&counter[1]
    &counter[0]) | (counter[5]&counter[4]&!counter[2]&!counter[1]
    &counter[0]) | (counter[7]&!counter[1]) | (!counter[6]&counter[5]
    &counter[4]&!counter[3]&counter[1]) | (!counter[6]&!counter[5]
    &counter[4]&!counter[2]&counter[1]) | (!counter[7]&!counter[6]
    &!counter[3]&!counter[2]&counter[1]&counter[0]) | (!counter[6]
    &counter[5]&!counter[4]&counter[3]&counter[2]&!counter[0]) | (
    !counter[6]&!counter[5]&counter[4]&counter[3]&counter[1]&!counter[0]) | (
    !counter[7]&!counter[6]&!counter[5]&!counter[4]&counter[3]&counter[2]
    &counter[1]&counter[0]) | (counter[6]&counter[5]&!counter[1]) | (
    counter[6]&counter[4]&!counter[1]) | (!counter[4]&counter[2]
    &!counter[1]&!counter[0]) | (!counter[5]&!counter[4]&counter[3]
    &!counter[2]&!counter[1]) | (counter[6]&counter[2]&!counter[1]) | (
    !counter[4]&counter[3]&!counter[1]&!counter[0]) | (counter[5]
    &!counter[4]&counter[2]&!counter[1]) | (counter[4]&counter[3]
    &counter[2]&!counter[1]&counter[0]);

assign csr_addr[0] = (!counter[6]&!counter[5]&counter[4]&counter[3]&!counter[2]
    &!counter[0]) | (counter[5]&!counter[4]&!counter[3]&!counter[1]
    &counter[0]) | (!counter[6]&counter[5]&counter[4]&!counter[3]
    &!counter[1]&!counter[0]) | (!counter[6]&counter[5]&counter[4]
    &!counter[3]&counter[2]&!counter[0]) | (counter[7]&counter[0]) | (
    !counter[6]&counter[5]&counter[3]&counter[2]&!counter[1]&!counter[0]) | (
    !counter[6]&!counter[5]&counter[4]&counter[1]&!counter[0]) | (
    !counter[6]&counter[5]&!counter[4]&!counter[3]&!counter[2]&counter[1]
    &!counter[0]) | (!counter[7]&!counter[6]&!counter[5]&!counter[4]
    &!counter[3]&counter[2]&!counter[1]&!counter[0]) | (counter[6]
    &!counter[5]&!counter[4]&!counter[3]&!counter[2]&!counter[1]) | (
    counter[5]&counter[4]&counter[3]&counter[2]&counter[1]&counter[0]) | (
    counter[6]&counter[0]) | (counter[5]&!counter[2]&!counter[1]
    &counter[0]) | (!counter[5]&counter[4]&counter[3]&!counter[1]
    &counter[0]) | (!counter[4]&!counter[3]&counter[2]&counter[1]
    &counter[0]) | (!counter[4]&!counter[3]&!counter[2]&!counter[1]
    &counter[0]);

