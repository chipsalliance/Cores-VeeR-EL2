<script lang="ts">
    import '#lib/aesir/src/styles/aesir-global.css';
    import '#lib/aesir/src/styles/aesir-motion.css';
    import '#lib/aesir/src/styles/aesir-typography.css';
    import { AesirTabs, AesirButton, AesirIcon } from '#lib/aesir/src/index.js';

    import Overview from '#lib/components/overview.svelte';
    import History from '#lib/components/history.svelte';
    import Compare from '#lib/components/compare.svelte';

    // Keep in sync with the inline script in index.html
    const THEME_STORAGE_KEY = 'aesir-html-theme';

    const tabs = [
        { label: 'Overview', value: 'overview' },
        { label: 'History', value: 'history' },
        { label: 'Compare', value: 'compare' }
    ];

    let activeTab = $state('overview');
    // The initial theme is applied by index.html
    let dark = $state(document.documentElement.classList.contains('dark'));

    function toggleTheme() {
        dark = !dark;
        const theme = dark ? 'dark' : 'light';
        document.documentElement.classList.toggle('dark', dark);
        document.documentElement.dataset.theme = theme;
        // Only an explicit choice is stored, so the OS preference is followed until then
        try {
            localStorage.setItem(THEME_STORAGE_KEY, theme);
        } catch {
            // Storage may be unavailable (e.g. incognito mode)
        }
    }
</script>

<main class="page-width">
    <header class="page-header">
        <div class="tabs-wrap">
            <AesirTabs bind:value={activeTab} items={tabs} label="Metric views" variant="line" border />
        </div>

        <AesirButton variant="outline" size="sm" aria-label={dark ? 'Switch to light theme' : 'Switch to dark theme'} onclick={toggleTheme}>
            <AesirIcon name={dark ? 'sun' : 'moon'} size="16" />
            <span>{dark ? 'Light' : 'Dark'}</span>
        </AesirButton>
    </header>

    <section class="metric-views">
        {#if activeTab === 'compare'}
            <Compare />
        {:else if activeTab === 'history'}
            <History />
        {:else}
            <Overview />
        {/if}
    </section>
</main>

<style>
    :global {
        .page-width {
            width: min(calc(100% - var(--ds-spacing-8)), 95%);
            margin-inline: auto;
        }

        body {
            min-height: 100vh;
            margin: 0;
            background: var(--ds-background);
            color: var(--ds-foreground);
        }

        html.dark {
            color-scheme: dark;
        }
    }

    main {
        display: grid;
        gap: var(--ds-spacing-8);
        padding-block: var(--ds-spacing-8) var(--ds-spacing-20);
    }

    .page-header {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: var(--ds-spacing-4);
    }

    .tabs-wrap {
        flex: 0 0 auto;
    }

    .metric-views {
        min-width: 0;
    }

    @media (max-width: 640px) {
        main {
            padding-top: var(--ds-spacing-4);
        }

        .page-header {
            gap: var(--ds-spacing-2);
        }
    }
</style>
