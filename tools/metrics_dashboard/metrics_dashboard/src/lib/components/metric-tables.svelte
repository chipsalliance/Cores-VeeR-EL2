<script lang="ts" generics="T">
    import { AesirSeparator, AesirTable } from '#lib/aesir/src/index.js';
    import { alignColumns } from '#lib/aesir.ts';
    import type { Group, Section } from '#lib/metrics.ts';

    type Column = { key: string; label: string; align?: 'start' | 'center' | 'end' };

    let {
        groups,
        columns,
        toRows
    }: {
        groups: Group<T>[];
        columns: Column[];
        toRows: (group: Group<T>, section: Section<T>) => Record<string, unknown>[];
    } = $props();
</script>

<!-- One table per category -->
<div class="metric-tables" use:alignColumns>
    {#each groups as group (group.name)}
        <div class="subtable">
            <h3>{group.label}</h3>
            <AesirSeparator orientation="horizontal" />
            {#each group.sections as section (section.key)}
                {#if section.label}
                    <h4>{section.label}</h4>
                {/if}
                <AesirTable {columns} rows={toRows(group, section)} variant="striped" density="compact" />
            {/each}
        </div>
    {/each}
</div>

<style>
    .subtable {
        margin: 0 0 var(--ds-spacing-12) 0;
    }

    :global {
        .metric-tables table {
            table-layout: fixed;
            width: 100%;
        }

        .metric-tables.measuring table {
            table-layout: auto;
            width: auto;
        }
    }
</style>
