<script lang="ts">
    import { Data } from '#lib/data.ts';
    import { summaryRows, type Run } from '#lib/metrics.ts';
    import { AesirCard } from '#lib/aesir/src/index.js';

    let { title = 'Summary', run }: { title?: string; run: Run } = $props();

    // Metrics listed in the config's summary
    let rows = $derived(summaryRows('branch/main', Data, run.index));
</script>

<AesirCard {title} class="version-panel">
    {#if rows.length}
        <table class="summary">
            <tbody>
                {#each rows as { key, label, value } (key)}
                    <tr>
                        <th scope="row">{label}</th>
                        <td>{value}</td>
                    </tr>
                {/each}
            </tbody>
        </table>
    {:else}
        <p class="empty">No summary metrics configured.</p>
    {/if}
</AesirCard>

<style>
    :global(.version-panel) {
        display: grid;
        align-content: start;
        gap: var(--ds-spacing-3);
        border: var(--ds-spacing-px) solid var(--ds-accent-border);
        border-radius: var(--ds-radius-lg);
    }

    .summary {
        width: 100%;
        border-spacing: 0;
        font-size: var(--ds-font-size-s);
    }

    .summary th,
    .summary td {
        padding: var(--ds-spacing-1) var(--ds-spacing-3);
    }

    .summary th {
        text-align: left;
        color: var(--ds-foreground-muted);
        font-weight: var(--ds-font-weight-normal);
    }

    .summary td {
        text-align: right;
        font-variant-numeric: tabular-nums;
    }

    .empty {
        margin: 0;
        color: var(--ds-foreground-muted);
        font-size: var(--ds-font-size-sm);
    }
</style>
