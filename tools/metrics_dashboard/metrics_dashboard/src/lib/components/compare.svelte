<script lang="ts">
    import { AesirButton, AesirCard } from '#lib/aesir/src/index.js';
    import { Data } from '#lib/data.ts';
    import {
        diffRuns,
        formatDiff,
        formatValues,
        groupByCategory,
        refTitle,
        sortedRefs,
        type Run,
        type Group,
        type Section,
        type MetricDiff
    } from '#lib/metrics.ts';

    import MetricTables from '#lib/components/metric-tables.svelte';
    import RunPicker from '#lib/components/run-picker.svelte';
    import Summary from '#lib/components/summary.svelte';

    // Runs of every ref: the main branch first, newest first within a ref
    const data = Data;
    const refs =
        data === null
            ? []
            : sortedRefs(data).flatMap((ref) => {
                  const runs = data.runs.get(ref.key) ?? [];
                  return runs.length ? [{ ...ref, title: refTitle(ref), runs }] : [];
              });
    const runs = refs.flatMap((ref) => ref.runs);
    const titles = new Map(refs.map((ref) => [ref.key, ref.title]));
    const runTitle = (run: Run) => `${titles.get(run.ref)} · ${run.label}`;

    // Runs grouped under their branch or PR
    const items = refs.flatMap((ref, i) => [
        ...(i ? [{ type: 'separator' as const }] : []),
        { type: 'label' as const, label: ref.title },
        ...ref.runs.map((run) => ({ label: run.label, value: run.value }))
    ]);

    // Compare the newest run against the one before it as default
    let target = $state.raw(runs[0]);
    let base = $state.raw(runs[1]);
    // The selection is compared upon button click
    let compared = $state.raw<{ target: Run; base: Run } | null>(null);

    let diffs = $derived(Data && compared ? diffRuns(Data, compared.base, compared.target) : []);
    let groups = $derived(Data ? groupByCategory(diffs, (d) => d.metric.path, Data.config) : []);

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
        <RunPicker label={title} {run} {runs} {items} {runTitle} onselect={select} />
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
        <MetricTables {groups} columns={compColumns} {toRows} />
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
</style>
