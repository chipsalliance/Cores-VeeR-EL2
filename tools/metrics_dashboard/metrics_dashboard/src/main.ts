import { flushSync, mount } from 'svelte';
import '#lib/aesir-html/components/aesir-loader.min.js';
import App from './app.svelte';

// Wait two frames so the browser paints the loader before the (blocking) chart rendering starts
await new Promise((resolve) => requestAnimationFrame(() => requestAnimationFrame(resolve)));

const loader = document.getElementById('page-loader');
let app;

try {
    app = mount(App, { target: document.getElementById('app')! });
    flushSync();
    loader?.remove();
} catch (e) {
    console.error(e);
    if (loader) loader.textContent = 'Failed to load the dashboard, see the browser console for details.';
}

export default app;
