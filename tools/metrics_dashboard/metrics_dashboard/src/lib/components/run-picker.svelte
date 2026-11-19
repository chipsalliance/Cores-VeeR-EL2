<script lang="ts">
    import { AesirDropdown, AesirButton, AesirIcon } from '#lib/aesir/src/index.js';
    import type { DropdownItem } from '#lib/aesir/src/components/aesir-dropdown/types.ts';
    import type { Run } from '#lib/metrics.ts';

    let {
        label,
        run,
        runs,
        items = runs.map((r) => ({ label: r.label, value: r.value })),
        runTitle = (r: Run) => r.label,
        onselect
    }: {
        // Picker name
        label: string;
        run: Run;
        runs: readonly Run[];
        // Dropdown entries
        items?: DropdownItem[];
        runTitle?: (run: Run) => string;
        onselect: (run: Run) => void;
    } = $props();
</script>

<!-- The menu is portaled to <body> below dialogs (z-index 50 < 70): raise it so it opens over the run details -->
<AesirDropdown
    {items}
    contentStyle="z-index: calc(var(--aesir-overlay-z-dialog, 70) + 1);"
    matchTriggerWidth
    onselect={(item) => {
        const selected = runs.find((r) => r.value === item.value);
        if (selected) onselect(selected);
    }}
>
    {#snippet trigger(props)}
        <AesirButton variant="outline" {...props} aria-label={`${label} run: ${runTitle(run)}`}
            >{runTitle(run)}<AesirIcon name="chevron-down" /></AesirButton
        >
    {/snippet}
</AesirDropdown>
