<script lang="ts">
    import { AesirBadge, AesirButton, AesirCard, AesirIcon, AesirTable } from '#lib/aesir/src/index.js';
    import { Data } from '#lib/data.ts';
    import { overviewCards } from '#lib/metrics.ts';

    const cards = overviewCards(Data);
    const metricRows = Math.max(Data.config.overview?.length ?? 0, 1);

    const cardColumns = [
        { key: 'label', label: 'label' },
        { key: 'value', label: 'value', align: 'end' as const }
    ];
</script>

{#if cards.length}
    <!-- All cards are the same size -->
    <div class="overview" style:--metric-rows={metricRows} style:--card-rows={metricRows + 2}>
        {#each cards as card (card.key)}
            <AesirCard class="overview-card" title={card.title} titleElement="h2" description={card.description}>
                {#snippet headerAction()}
                    <div class="overview-card__status">
                        {#if card.url}
                            <a
                                class="overview-card__link"
                                href={card.url}
                                target="_blank"
                                rel="noopener noreferrer"
                                aria-label={`Open ${card.title}`}
                            >
                                <AesirIcon name="external-link" size="16" />
                            </a>
                        {/if}
                        <AesirBadge variant={card.badge.variant}>{card.badge.label}</AesirBadge>
                    </div>
                {/snippet}

                <dl class="overview-card__metrics">
                    <AesirTable columns={cardColumns} rows={card.rows} showHeader={false} density="sm" variant="minimal" />
                </dl>

                {#snippet footer()}
                    <span class="overview-card__updated">Last updated: <time>{card.updated}</time></span>
                    <AesirButton size="sm" variant="outline">View details</AesirButton>
                {/snippet}
            </AesirCard>
        {/each}
    </div>
{:else}
    <p class="empty">No runs yet.</p>
{/if}

<style>
    .overview {
        display: grid;
        grid-template-columns: repeat(auto-fill, minmax(min(var(--ds-sizing-xs), 100%), 1fr));
        column-gap: var(--ds-spacing-6);
        max-width: var(--ds-sizing-7xl);
        margin-inline: auto;
    }

    .overview :global(.overview-card) {
        display: grid;
        grid-row: span var(--card-rows);
        grid-template-rows: subgrid;
        row-gap: 0;
        margin-block-end: var(--ds-spacing-10);
    }

    .overview :global(.overview-card .aesir-card__header) {
        align-content: start;
        padding-bottom: var(--ds-spacing-6);
    }

    .overview :global(.overview-card .aesir-card__title) {
        margin: 0;
        font-size: var(--ds-font-size-base);
    }

    .overview :global(.overview-card .aesir-card__content) {
        display: contents;
    }

    .overview :global(.overview-card .aesir-card__footer) {
        flex-wrap: wrap;
        justify-content: space-between;
        align-self: end;
        padding-top: var(--ds-spacing-6);
    }

    .overview :global(.overview-card .aesir-card__footer > :last-child) {
        margin-inline-start: auto;
    }

    .overview-card__status {
        display: flex;
        flex-shrink: 0;
        align-items: center;
        gap: var(--ds-spacing-2);
    }

    .overview-card__link {
        display: inline-flex;
        color: var(--ds-foreground-muted);
    }

    .overview-card__link:hover,
    .overview-card__link:focus-visible {
        color: var(--ds-foreground);
    }

    .overview-card__metrics {
        display: grid;
        grid-row: span var(--metric-rows);
        grid-template-rows: subgrid;
        row-gap: 0;
        padding-inline: var(--ds-spacing-6);
        grid-template-columns: minmax(0, 1fr) auto;
        column-gap: var(--ds-spacing-4);
        margin: 0;
        font-size: var(--ds-font-size-sm);
    }

    .overview-card__updated {
        color: var(--ds-foreground-muted);
        font-size: var(--ds-font-size-xs);
    }
</style>
