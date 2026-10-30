import { svelte } from '@sveltejs/vite-plugin-svelte';
import { defineConfig } from 'vitest/config';
import { viteSingleFile } from 'vite-plugin-singlefile';

export default defineConfig({
    base: './',
    plugins: [svelte(), viteSingleFile()],
    build: {
        outDir: 'build'
    },
    test: {
        include: ['src/**/*.test.ts'],
        // Skip Aesir tests
        exclude: ['src/lib/aesir/**', 'src/lib/aesir-html/**']
    }
});
