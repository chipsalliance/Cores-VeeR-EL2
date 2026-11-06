<script lang="ts">
    import { Data } from '#lib/data.ts';
    import { MAIN_REF, summaryRows, type Run } from '#lib/metrics.ts';
    import { AesirCard, AesirTable } from '#lib/aesir/src/index.js';

    let { title = 'Summary', run }: { title?: string; run: Run } = $props();

    // Metrics and metadata fields from the config's summary
    let rows = $derived(summaryRows(MAIN_REF, Data, run, Data.config.summary));

    const cols = [
        { key: 'label', label: 'label' },
        { key: 'value', label: 'value', align: 'end' as const }
    ];
</script>

<AesirCard {title} class="version-panel">
    {#if rows.length}
        <AesirTable
            columns={cols}
            rows={rows.map((r) => ({ label: r.label, value: r.value }))}
            showHeader={false}
            density="sm"
            variant="minimal"
            class="summary"
        />
    {:else}
        <p class="empty">No summary metrics configured.</p>
    {/if}
</AesirCard>

<style>
    :global(.version-panel) {
        border: var(--ds-spacing-px) solid var(--ds-accent-border);
    }
</style>
