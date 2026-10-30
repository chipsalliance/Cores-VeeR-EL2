<script lang="ts">
    import { AesirBadge, AesirButton, AesirCard } from '#lib/aesir/src/index.js';
</script>

<div class="overview">
    {#each Array.from({ length: 30 }, (_, x) => x + 1) as id (id)}
        <div class="pr-card">
            <AesirCard title="PR # {id}" description="PR title (name#{id})">
                {#snippet headerAction()}<AesirBadge variant={id % 3 === 0 ? 'success' : id % 3 === 1 ? 'warning' : 'destructive'}
                        >{id % 3 === 0 ? 'pass' : id % 3 === 1 ? 'warning' : 'fail'}</AesirBadge
                    >{/snippet}

                <div class="project-card">
                    <dl class="project-card__metrics">
                        <div>
                            <dt>Errors</dt>
                            <dd>0</dd>
                        </div>
                        <div>
                            <dt>Warnings</dt>
                            <dd>42</dd>
                        </div>
                        <div>
                            <dt>Runtime</dt>
                            <dd>{id ** 2}h</dd>
                        </div>
                    </dl>
                </div>

                {#snippet footer()}
                    <div class="project-card__footer">
                        <span>Last updated: {id} minutes ago</span>
                        <AesirButton size="sm" variant="outline">View latest run</AesirButton>
                    </div>
                {/snippet}
            </AesirCard>
        </div>
    {/each}
</div>

<style>
    .overview {
        display: grid;
        grid-template-columns: repeat(auto-fill, minmax(min(var(--ds-sizing-xs), 100%), 1fr));
        gap: var(--ds-spacing-10);
        margin-inline: auto;
        max-width: var(--ds-sizing-7xl);
    }

    .pr-card {
        width: var(--ds-sizing-s);
        height: auto;
    }

    .project-card {
        width: 100%;
        display: grid;
        gap: var(--ds-spacing-5);
    }

    .project-card__metrics {
        display: grid;
        grid-template-columns: repeat(3, minmax(0, 1fr));
        margin: 0;
    }

    .project-card__metrics div {
        padding-inline: var(--ds-spacing-4);
        border-left: var(--ds-spacing-px) solid var(--ds-border);
    }

    .project-card__metrics div:first-child {
        padding-left: 0;
        border-left: 0;
    }

    .project-card__metrics dt {
        color: var(--ds-foreground-muted);
        font-size: var(--ds-font-size-xs);
    }

    .project-card__metrics dd {
        margin: var(--ds-spacing-1) 0 0;
        font-size: var(--ds-font-size-lg);
        font-weight: var(--ds-font-weight-medium);
    }

    .project-card__footer {
        display: flex;
        width: 100%;
        align-items: center;
        justify-content: space-between;
        gap: var(--ds-spacing-4);
        color: var(--ds-foreground-muted);
        font-size: var(--ds-font-size-xs);
    }

    @media (max-width: 479px) {
        .project-card__metrics {
            grid-template-columns: 1fr;
            gap: var(--ds-spacing-3);
        }

        .project-card__metrics div {
            padding: 0;
            border-left: 0;
        }

        .project-card__footer {
            align-items: flex-start;
            flex-direction: column;
        }
    }
</style>
