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

describe('valueTickFormat', () => {
    it('uses SI prefixes for large and tiny values', () => {
        expect(mt.valueTickFormat([0, 25000])(25000)).toBe('25k');
        expect(mt.valueTickFormat([0.001])(0.001)).toBe('1m');
    });

    it('handles empty input', () => {
        expect(mt.valueTickFormat([])(5)).toBe('5');
    });
});

describe('units', () => {
    it('labels axes with the unit', () => {
        expect(mt.axisLabel({ label: 'Area', unit: 'um^2' })).toBe('Area [um^2]');
        expect(mt.axisLabel({ label: 'Runtime', unit: 's' })).toBe('Runtime [h:mm:ss]');
    });

    it('formats single values with their unit', () => {
        expect(mt.formatValue(25000, 'um^2')).toBe('25k um^2');
        expect(mt.formatValue(42, '')).toBe('42');
    });
});

describe('formatPercent', () => {
    it('is signed with two decimals', () => {
        expect(mt.formatPercent(12.345)).toBe('+12.35%');
        // d3 uses U+2212
        expect(mt.formatPercent(-3)).toBe('−3.00%');
        expect(mt.formatPercent(0)).toBe('0%');
    });
});
