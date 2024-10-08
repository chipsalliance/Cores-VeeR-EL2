#include <stdio.h>

int handler() __attribute__((section(".handler")));

int handler() {
    return 0;
}

int main () {
    int (*func)() = (int (*)())0x70000001;
    printf("jumping to 0x70000001\n");
    func();
    printf("jumping to 0x80001\n");
    func = 0x80001;
    func();
    printf("jumping to 0xe000001\n");
    func = 0xe000001;
    func();
    return 0;
}
