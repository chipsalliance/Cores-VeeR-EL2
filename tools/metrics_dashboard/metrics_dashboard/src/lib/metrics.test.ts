import { describe, expect, it } from 'vitest';
import * as mt from '#lib/metrics.ts';

describe('parseDate', () => {
    it('parses the flow date format', () => {
        expect(mt.parseDate(' 2026-05-31 21:52 ')).toEqual(new Date(2026, 4, 31, 21, 52));
    });

    it('rejects other values', () => {
        expect(mt.parseDate('31.05.2026')).toBeNull();
        expect(mt.parseDate(1234)).toBeNull();
        expect(mt.parseDate(null)).toBeNull();
    });
});

describe('units', () => {
    it('labels axes with the unit', () => {
        expect(mt.axisLabel({ label: 'Area', unit: 'um^2' })).toBe('Area [µm²]');
        expect(mt.axisLabel({ label: 'Runtime', unit: 's' })).toBe('Runtime [h:mm:ss]');
    });

    it('formats single values with their unit', () => {
        expect(mt.formatValue(25000, 'um^2')).toBe('25,000 µm²');
        expect(mt.formatValue(0.000860818, 'mW')).toBe('860.818 nW');
        expect(mt.formatValue(42, '')).toBe('42');
    });

    it('formats values of a comparison in one unit', () => {
        expect(mt.formatValues([0.000999, 0.00101], 'mW')).toEqual(['0.999 µW', '1.01 µW']);
    });

    it('picks one display unit per axis', () => {
        const axis = mt.valueAxis({ label: 'Power', unit: 'mW' }, [0.00086, 0.0009]);
        expect([axis.label, axis.unit, axis.format(0.00087)]).toEqual(['Power [nW]', 'nW', '870']);
    });
});

describe('formatPercent', () => {
    it('with two decimals', () => {
        expect(mt.formatDiff(12.345, 0.11)).toBe('−12.24 (−99.11%)');
        expect(mt.formatDiff(-3, 6)).toBe('+9 (+300%)');
        expect(mt.formatDiff(0, 0)).toBe('−');
        expect(mt.formatDiff(4, 4)).toBe('−');
    });
});

describe('empty data', () => {
    const dataset = mt.buildDataset({ metrics: [], refs: [] }, { labels: {}, units: {} });

    it('has no run, metrics or references', () => {
        expect(dataset.refs).toEqual([]);
        expect(dataset.runs.get(mt.MAIN_REF)).toBeUndefined();
        expect(dataset.metrics.get(mt.MAIN_REF)).toBeUndefined();
        expect(mt.seriesFor(mt.MAIN_REF, dataset, mt.dateAxis())).toBeNull();
        expect(mt.latestValue(dataset, mt.MAIN_REF, 'a.b')).toBeNull();
    });
});
