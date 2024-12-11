#define STDOUT 0xd0580000

/* TODO remove this. It's not supported by the testbench mailbox logic */
#define LOAD_NMI_ADDR 0x81
/* helper macros that define messages to be written to `STDOUT` to trigger and clear interrupts */

#define CLEAR 0x82
#define TRIGGER 0x83

#define NMI_INT (1<<8)
#define TIMER_INT (1<<9)
#define SOFT_INT (1<<10)

#define TRIGGER_NMI_INT (TRIGGER | NMI_INT)
#define TRIGGER_TIMER_INT (TRIGGER | TIMER_INT)
#define TRIGGER_SOFT_INT (TRIGGER | SOFT_INT)

#define CLEAR_NMI_INT (CLEAR | NMI_INT)
#define CLEAR_TIMER_INT (CLEAR | TIMER_INT)
#define CLEAR_SOFT_INT (CLEAR | SOFT_INT)
