<script lang="ts">
    import { AesirDropdown, AesirButton, AesirIcon, AesirCard } from '#lib/aesir/src/index.js';
    import { Data } from '#lib/data.ts';
    import { diffRuns, formatPercent, formatValue, groupByCategory, type Run } from '#lib/metrics.ts';

    import Summary from '#lib/components/summary.svelte';
    const runs = Data.runs;

    const byValue = (value: string | null | undefined) => runs.get('branch/main')!.find((r) => r.value === value);

    // Compare the newest run against the one before it as default
    let targetValue = $state(runs.get('branch/main')![0]?.value);
    let baseValue = $state(runs.get('branch/main')![1]?.value);

    // Perform the diff upon button click (keep the states)
    let confirmedTargetValue = $state<string | null>(null);
    let confirmedBaseValue = $state<string | null>(null);

    let target = $derived(byValue(targetValue));
    let base = $derived(byValue(baseValue));
    let confirmedTarget = $derived(byValue(confirmedTargetValue));
    let confirmedBase = $derived(byValue(confirmedBaseValue));
    let sameVersion = $derived(targetValue === baseValue);

    let diffs = $derived(
        confirmedTarget && confirmedBase ? diffRuns(Data.metrics.get('branch/main')!, confirmedBase.index, confirmedTarget.index) : []
    );
    let groups = $derived(groupByCategory(diffs, (d) => d.metric.path, Data.config));

    function confirmComparison() {
        if (sameVersion) return;
        confirmedTargetValue = targetValue;
        confirmedBaseValue = baseValue;
    }
</script>

{#snippet versionPanel(title: string, run: Run, select: (value: string) => void)}
    <AesirCard {title}>
        <AesirDropdown items={runs.get('branch/main')!} onselect={(item) => item.value && select(item.value)}>
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
                {@render versionPanel('Target', target, (value) => (targetValue = value))}
                {@render versionPanel('Base', base, (value) => (baseValue = value))}
            </div>

            <div class="actions">
                {#if sameVersion}
                    <p class="error" role="alert">Please select two different runs.</p>
                {/if}
                <AesirButton onclick={confirmComparison} disabled={sameVersion}>Compare</AesirButton>
            </div>
        {:else}
            <p class="error">At least two runs are needed for a comparison.</p>
        {/if}

        {#if confirmedTarget && confirmedBase}
            <div class="version-grid">
                <Summary title="Target summary" run={confirmedTarget}></Summary>
                <Summary title="Base summary" run={confirmedBase}></Summary>
            </div>
        {/if}
    </section>

    {#if confirmedTarget && confirmedBase}
        <div>
            <table class="comparison-table">
                <thead>
                    <tr>
                        <th scope="col">Metric</th>
                        <th scope="col">Base</th>
                        <th scope="col">Target</th>
                        <th scope="col">Change</th>
                    </tr>
                </thead>
                {#each groups as group (group.name)}
                    <tbody>
                        <tr class="group">
                            <th scope="rowgroup" colspan="4">{group.label}</th>
                        </tr>
                        {#each group.sections as section (section.key)}
                            {#if section.label}
                                <tr class="section">
                                    <th scope="rowgroup" colspan="4">{section.label}</th>
                                </tr>
                            {/if}
                            {#each section.items as d (d.metric.key)}
                                <tr>
                                    <th scope="row">{d.metric.label}</th>
                                    <td>{formatValue(d.base, d.metric.unit)}</td>
                                    <td>{formatValue(d.target, d.metric.unit)}</td>
                                    <td class="change" class:unchanged={d.percent === 0}>{d.percent === null ? 'n/a' : formatPercent(d.percent)}</td>
                                </tr>
                            {/each}
                        {/each}
                    </tbody>
                {/each}
            </table>
        </div>
    {/if}
</div>

<style>
    .compare-page {
        display: grid;
        grid-template-columns: minmax(0, 1fr);
        gap: var(--ds-spacing-8);
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

    .comparison-table {
        width: 100%;
        border-collapse: separate;
        border-spacing: 0;
        border: var(--ds-spacing-px) solid var(--ds-border);
        border-radius: var(--ds-radius-lg);
    }

    .comparison-table tr > :is(th, td) {
        border-bottom: var(--ds-spacing-px) solid var(--ds-border);
    }

    .comparison-table tbody:last-child tr:last-child > :is(th, td) {
        border-bottom: none;
    }

    .comparison-table tr.group th {
        font-weight: var(--ds-font-weight-semibold);
        background: var(--ds-background-secondary);
    }

    .comparison-table tr.section th {
        font-size: var(--ds-font-size-xs);
        font-weight: var(--ds-font-weight-semibold);
        color: var(--ds-foreground-muted);
    }

    .comparison-table th,
    .comparison-table td {
        padding: var(--ds-spacing-2-5) var(--ds-spacing-3);
    }

    .comparison-table th {
        text-align: left;
        font-weight: var(--ds-font-weight-normal);
    }

    .comparison-table thead th {
        font-size: var(--ds-font-size-xs);
        font-weight: var(--ds-font-weight-semibold);
        color: var(--ds-foreground-muted);
    }

    .comparison-table thead th:not(:first-child) {
        text-align: right;
    }

    .comparison-table td {
        text-align: right;
        font-variant-numeric: tabular-nums;
        color: var(--ds-foreground-muted);
    }

    .comparison-table td.change {
        color: var(--ds-foreground);
        font-weight: var(--ds-font-weight-medium);
    }

    .comparison-table td.change.unchanged {
        color: var(--ds-foreground-muted);
        font-weight: var(--ds-font-weight-normal);
    }
</style>
