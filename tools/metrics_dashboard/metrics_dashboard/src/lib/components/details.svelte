<script lang="ts">
    import { AesirBadge, AesirButton, AesirDialog, AesirIcon, AesirTable } from '#lib/aesir/src/index.js';
    import { Data } from '#lib/data.ts';
    import {
        formatParam,
        groupByCategory,
        metadataRows,
        pipelineBadge,
        refTitle,
        runParams,
        type Configuration,
        type Group,
        type Run,
        type RunParam,
        type Section
    } from '#lib/metrics.ts';
    import MetricTables from '#lib/components/metric-tables.svelte';
    import RunPicker from '#lib/components/run-picker.svelte';

    // Details of the runs of one branch or PR and configuration, opened on its latest run
    let { refKey, configuration = null, open = $bindable(false) }: { refKey: string; configuration?: Configuration; open?: boolean } = $props();

    let ref = $derived(Data?.refs.find((r) => r.key === refKey));
    let runs = $derived((Data?.runs.get(refKey) ?? []).filter((r) => r.configuration === configuration));
    let picked = $state.raw<Run | null>(null);
    let run = $derived(picked && picked.ref === refKey ? picked : runs[0]);

    let badge = $derived(pipelineBadge(run?.metadata.pipeline_status));
    let metadata = $derived(Data && run ? metadataRows(Data, run) : []);
    let groups = $derived(Data && run ? groupByCategory(runParams(Data, run), (p) => p.metric.path, Data.config) : []);

    const metadataColumns = [
        { key: 'label', label: 'Field' },
        { key: 'value', label: 'Value', align: 'end' as const }
    ];

    const valueColumns = [
        { key: 'metric', label: 'Metric' },
        { key: 'value', label: 'Value', align: 'end' as const }
    ];

    const toRows = (g: Group<RunParam>, s: Section<RunParam>) =>
        s.items.map((p) => ({
            id: `${g.name}/${s.key}/${p.metric.key}`,
            metric: p.metric.label,
            value: formatParam(p.value, p.metric.unit)
        }));
</script>

<AesirDialog
    bind:open
    title={[ref ? refTitle(ref) : refKey, configuration].filter(Boolean).join(' · ')}
    description={run?.metadata.pr_title}
    closeLabel="Close run details"
    class="run-details"
>
    {#if run}
        <div class="run-details__toolbar">
            <RunPicker label="Details" {run} {runs} onselect={(r) => (picked = r)} />
            <AesirBadge variant={badge.variant}>{badge.label}</AesirBadge>
            {#if run.metadata.url}
                <AesirButton href={run.metadata.url} target="_blank" rel="noopener noreferrer" variant="outline" size="sm">
                    Open run<AesirIcon name="external-link" size="16" />
                </AesirButton>
            {/if}
        </div>

        {#if metadata.length}
            <AesirTable columns={metadataColumns} rows={metadata} showHeader={false} density="sm" variant="minimal" class="run-details__metadata" />
        {/if}

        {#if groups.length}
            <MetricTables {groups} columns={valueColumns} {toRows} />
        {:else}
            <p class="empty">No metrics reported by this run.</p>
        {/if}
    {:else}
        <p class="empty">No runs yet.</p>
    {/if}
</AesirDialog>

<style>
    :global(.aesir-dialog.run-details) {
        width: min(100%, var(--ds-sizing-4xl));
    }

    :global(.run-details .aesir-dialog__body) {
        display: grid;
        gap: var(--ds-spacing-6);
        color: var(--ds-foreground);
    }

    .run-details__toolbar {
        display: flex;
        flex-wrap: wrap;
        align-items: center;
        gap: var(--ds-spacing-3);
    }

    .run-details__toolbar > :global(:last-child) {
        margin-inline-start: auto;
    }
</style>
