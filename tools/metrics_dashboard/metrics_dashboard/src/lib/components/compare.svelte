<script lang="ts">
    import { AesirDropdown, AesirButton, AesirIcon, AesirCard, AesirTable, AesirSeparator } from '#lib/aesir/src/index.js';
    import { Data } from '#lib/data.ts';
    import {
        diffRuns,
        formatDiff,
        formatValues,
        groupByCategory,
        MAIN_REF,
        type Run,
        type Group,
        type Section,
        type MetricDiff
    } from '#lib/metrics.ts';
    import { alignColumns } from '#lib/aesir.ts';

    import Summary from '#lib/components/summary.svelte';
    const runs = Data.runs.get(MAIN_REF) ?? [];

    // Compare the newest run against the one before it as default
    let target = $state.raw(runs[0]);
    let base = $state.raw(runs[1]);
    // The selection is compared upon button click
    let compared = $state.raw<{ target: Run; base: Run } | null>(null);

    let diffs = $derived(compared ? diffRuns(Data.metrics.get(MAIN_REF) ?? [], compared.base.index, compared.target.index) : []);
    let groups = $derived(groupByCategory(diffs, (d) => d.metric.path, Data.config));

    const compColumns = [
        { key: 'metric', label: 'Metric' },
        { key: 'base', label: 'Base' },
        { key: 'target', label: 'Target' },
        { key: 'change', label: 'Change', align: 'end' as const }
    ];

    const toRows = (g: Group<MetricDiff>, s: Section<MetricDiff>) =>
        s.items.map((d) => {
            const [base, target] = formatValues([d.base, d.target], d.metric.unit);
            return {
                id: `${g.name}/${s.key}/${d.metric.key}`,
                metric: d.metric.label,
                base,
                target,
                change: formatDiff(d.base, d.target)
            };
        });
</script>

{#snippet versionPanel(title: string, run: Run, select: (run: Run) => void)}
    <AesirCard {title}>
        <AesirDropdown
            items={runs}
            onselect={(item) => {
                const selected = runs.find((r) => r.value === item.value);
                if (selected) select(selected);
            }}
        >
            {#snippet trigger(props)}
                <AesirButton variant="outline" {...props} aria-label={`${title} run: ${run.label}`}
                    >{run.label}<AesirIcon name="chevron-down" /></AesirButton
                >
            {/snippet}
        </AesirDropdown>
    </AesirCard>
{/snippet}

<div class="compare-page">
    <section class="comparison">
        <header class="heading">
            <h2>Compare results</h2>
            <p>Select references for comparison.</p>
        </header>

        {#if target && base}
            <div class="version-grid">
                {@render versionPanel('Target', target, (run) => (target = run))}
                {@render versionPanel('Base', base, (run) => (base = run))}
            </div>

            <div class="actions">
                {#if target === base}
                    <p class="error" role="alert">Please select two different runs.</p>
                {/if}
                <AesirButton onclick={() => (compared = { target, base })} disabled={target === base}>Compare</AesirButton>
            </div>
        {:else}
            <p class="error">At least two runs are needed for a comparison.</p>
        {/if}

        {#if compared}
            <div class="version-grid">
                <Summary title="Target summary" run={compared.target}></Summary>
                <Summary title="Base summary" run={compared.base}></Summary>
            </div>
        {/if}
    </section>

    {#if compared}
        <div class="comparison-table" use:alignColumns>
            <section>
                {#each groups as group (group.name)}
                    <div class="subtable">
                        <h3>{group.label}</h3>
                        <AesirSeparator orientation="horizontal" />
                        {#each group.sections as section (section.key)}
                            {#if section.label}
                                <h4>{section.label}</h4>
                            {/if}
                            <AesirTable columns={compColumns} rows={toRows(group, section)} variant="striped" density="compact" />
                        {/each}
                    </div>
                {/each}
            </section>
        </div>
    {/if}
</div>

<style>
    .compare-page {
        display: grid;
        grid-template-columns: minmax(0, 1fr);
        gap: var(--ds-spacing-4);
        width: 100%;
        max-width: var(--ds-sizing-7xl);
        margin-inline: auto;
    }

    .comparison {
        display: grid;
        gap: var(--ds-spacing-3);
    }

    .heading h2 {
        margin: 0;
        font-size: var(--ds-font-size-xl);
    }

    .heading p {
        margin: var(--ds-spacing-1) 0 0;
        color: var(--ds-foreground-muted);
        font-size: var(--ds-font-size-sm);
    }

    .version-grid {
        display: grid;
        grid-template-columns: repeat(2, minmax(0, 1fr));
        gap: var(--ds-spacing-4);
    }

    .actions {
        display: flex;
        align-items: center;
        justify-content: flex-end;
        gap: var(--ds-spacing-3);
    }

    .error {
        margin: 0;
        color: var(--ds-foreground-red);
        font-size: var(--ds-font-size-sm);
    }

    .actions .error {
        margin-inline-end: auto;
    }

    @media (max-width: 640px) {
        .version-grid {
            grid-template-columns: 1fr;
        }
    }

    .subtable {
        margin: 0 0 var(--ds-spacing-12) 0;
    }

    :global {
        .comparison-table table {
            table-layout: fixed;
            width: 100%;
        }

        .comparison-table.measuring table {
            table-layout: auto;
            width: auto;
        }
    }
</style>
