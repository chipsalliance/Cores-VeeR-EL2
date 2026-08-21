# Triple Modular Redundancy (TMR)

This chapter describes the TMR feature of VeeR EL2 core.
When enabled, the top-level module instantiates 3 independent but synchronized VeeR cores along with majority voting, error detection and recovery logic.

```{note}
The following documentation describes planned TMR architecture and implementation which is subject to changes.
Also, at the moment the complete TMR functionality isn't implemented yet.
```

## Configuration

To enable the TMR feature pass the following options to the `veer.config` script:
```
-set=triple_modular_redundancy_enable=1
```
