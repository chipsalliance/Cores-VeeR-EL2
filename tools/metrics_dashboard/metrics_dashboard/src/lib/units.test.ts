import { describe, expect, it } from 'vitest';
import { displayScale, parseSiUnit } from '#lib/units.ts';

const show = (unit: string, ...values: number[]) => {
    const scale = displayScale(unit, values);
    return values.map((v) => `${scale.format(v)} ${scale.unit}`.trim());
};

describe('parseSiUnit', () => {
    it('reads prefixes, base units and powers', () => {
        expect(parseSiUnit('mW')).toEqual({ exponent: -3, base: 'W', power: 1 });
        expect(parseSiUnit('um^2')).toEqual({ exponent: -6, base: 'm', power: 2 });
        expect(parseSiUnit('µm**2')).toEqual({ exponent: -6, base: 'm', power: 2 });
        expect(parseSiUnit('kohm')).toEqual({ exponent: 3, base: 'ohm', power: 1 });
        expect(parseSiUnit('GHz')).toEqual({ exponent: 9, base: 'Hz', power: 1 });
    });

    it('prefers bare base units', () => {
        expect(parseSiUnit('m')).toEqual({ exponent: 0, base: 'm', power: 1 });
        expect(parseSiUnit('Pa')).toEqual({ exponent: 0, base: 'Pa', power: 1 });
        expect(parseSiUnit('T')).toEqual({ exponent: 0, base: 'T', power: 1 });
        expect(parseSiUnit('ms')).toEqual({ exponent: -3, base: 's', power: 1 });
    });

    it('rejects custom units', () => {
        for (const unit of ['', '%', 'cells', 'min', 'W/m', 'ratio', 'um^2/s', 'xW']) expect(parseSiUnit(unit)).toBeNull();
    });
});

describe('displayScale', () => {
    it('picks the prefix that keeps the numbers readable', () => {
        expect(show('mW', 0.000860818)).toEqual(['860.818 nW']);
        expect(show('W', 2.57805e-8)).toEqual(['25.7805 nW']);
        expect(show('Hz', 4229325260.0373)).toEqual(['4.22933 GHz']);
        expect(show('ps', -88.6054)).toEqual(['−88.6054 ps']);
        expect(show('ns', 1500)).toEqual(['1.5 µs']);
    });

    it('scales units with powers by the power', () => {
        expect(show('um^2', 4833.3856)).toEqual(['4,833.39 µm²']);
        expect(show('um^2', 2.5e7)).toEqual(['25 mm²']);
    });

    it('uses one unit for all the values', () => {
        expect(show('mW', 0.0009, 0.000001)).toEqual(['900 nW', '1 nW']);
    });

    it('keeps the unit for zeros and empty value sets', () => {
        expect(show('ps', 0)).toEqual(['0 ps']);
        expect(displayScale('mW', []).unit).toBe('mW');
    });

    it('shows scientific notation', () => {
        expect(show('%', 27.84)).toEqual(['27.84 %']);
        expect(show('cells', 1.2e6)).toEqual(['1.2e+6 cells']);
        expect(show('', 259)).toEqual(['259']);
        expect(show('', 0.0001)).toEqual(['1e-4']);
    });
});
