#define STDOUT 0xd0580000

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

#define TRIGGER_EXT_INT1 (0x81 | 1<<8)
#define CLEAR_EXT_INT1 (0x80 | 1<<8)
/* TODO these are not supported but used anyway. Remove them. */
#define TRIGGER_DBUS_FAULT 0
#define TRIGGER_IBUS_FAULT 0
