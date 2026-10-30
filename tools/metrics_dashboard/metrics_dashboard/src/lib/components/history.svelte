<script lang="ts">
    import type { Action } from 'svelte/action';
    import { AesirCollapsible } from '#lib/aesir/src/index.js';
    import { Data } from '#lib/data.ts';
    import { dateAxis, groupByCategory, seriesFor, valueAxis, type Series } from '#lib/metrics.ts';
    import { plot } from '#lib/plot.ts';
    import Summary from '#lib/components/summary.svelte';
    const axis = dateAxis(Data.config.date);
    const series = seriesFor('branch/main', Data, axis);
    const groups = groupByCategory(series ?? [], (s) => s.path, Data.config);
    const latest = Data.runs.get('branch/main')![0];

    const render = (s: Series<Date>) =>
        plot(
            s,
            axis,
            valueAxis(
                s,
                s.data.map((d) => d.param)
            )
        );

    // Render plot only on request (expand collapsible)
    const mountPlot: Action<HTMLElement, Series<Date>> = (node, s) => {
        let current = s;
        let chart: ReturnType<typeof render> | undefined;

        const observer = new IntersectionObserver(
            (entries) => {
                if (!entries.some((e) => e.isIntersecting)) return;
                observer.disconnect();
                node.append((chart = render(current)));
            },
            { rootMargin: '25% 0px' }
        );
        observer.observe(node);

        return {
            update(next) {
                current = next;
                if (chart) chart.replaceWith((chart = render(next)));
            },
            destroy() {
                observer.disconnect();
                chart?.remove();
            }
        };
    };
</script>

<div class="run-overview">
    {#if latest}
        <section class="summary">
            <Summary title="Latest run" run={latest}></Summary>
        </section>
    {/if}

    <section class="categories">
        {#each groups as group (group.name)}
            <AesirCollapsible title={group.label}>
                {#each group.sections as section (section.key)}
                    <section class="category-section">
                        {#if section.label}
                            <h3>{section.label}</h3>
                        {/if}
                        <div class="chart-grid">
                            {#each section.items as s (s.key)}
                                <div class="chart" use:mountPlot={s}></div>
                            {/each}
                        </div>
                    </section>
                {/each}
            </AesirCollapsible>
        {/each}
    </section>
</div>

<style>
    .run-overview {
        display: flex;
        flex-direction: column;
        gap: var(--ds-spacing-3);
        max-width: var(--ds-sizing-7xl);
        margin-inline: auto;
    }
    .categories {
        display: grid;
        gap: var(--ds-spacing-3);
    }

    .category-section + .category-section {
        margin-top: var(--ds-spacing-6);
    }

    .category-section h3 {
        margin: 0 0 var(--ds-spacing-2);
        font-size: var(--ds-font-size-sm);
        font-weight: var(--ds-font-weight-semibold);
        color: var(--ds-foreground-muted);
    }

    .chart-grid {
        display: grid;
        grid-template-columns: repeat(auto-fill, minmax(min(var(--ds-sizing-xl), 100%), 1fr));
        gap: var(--ds-spacing-2);
    }

    .chart-grid :global(svg) {
        max-width: 100%;
        height: auto;
        /* Plot's tooltip defaults to a white box */
        --plot-background: var(--ds-background);
    }
</style>
