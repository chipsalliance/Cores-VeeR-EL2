import { format, max } from 'd3';

const SI = ['q', 'r', 'y', 'z', 'a', 'f', 'p', 'n', 'µ', 'm', '', 'k', 'M', 'G', 'T', 'P', 'E', 'Z', 'Y', 'R', 'Q'] as const;

const PREFIXES: Readonly<Record<string, number>> = {
    ...Object.fromEntries(SI.map((p, i) => [p, (i - 10) * 3])),
    u: -6,
    '\u03bc': -6 // µ
};

const PREFIX_OF_EXPONENT = new Map(
    Object.entries(PREFIXES)
        .filter(([p]) => p !== 'u' && p !== 'μ')
        .map(([p, e]) => [e, p])
);

// Units that take SI prefixes
const BASE_UNITS = new Set(['m', 's', 'g', 'W', 'V', 'A', 'Hz', 'F', 'H', 'ohm', 'Ω', 'J', 'C', 'S', 'Wb', 'T', 'K', 'Pa', 'N', 'B', 'b', 'bit']);
// FIXME: find a better way to represent superscripts
const SUPERSCRIPTS: Readonly<Record<string, string>> = { '2': '²', '3': '³' };

type SiUnit = { exponent: number; base: string; power: number };

// 'mW' -> 10^-3 W, 'um^2' -> (10^-6 m)^2; null for units w/o the prefix (e.g. %)
export function parseSiUnit(unit: string): SiUnit | null {
    const match = /^([^\s^*/·]+?)(?:(?:\^|\*\*)([1-3]))?$/.exec(unit.trim());
    if (!match) return null;
    const [, symbol, power = '1'] = match;
    for (const [prefix, base] of [
        ['', symbol],
        [symbol.slice(0, 1), symbol.slice(1)]
    ]) {
        if (BASE_UNITS.has(base) && prefix in PREFIXES) return { exponent: PREFIXES[prefix], base, power: Number(power) };
    }
    return null;
}

function siUnitText({ exponent, base, power }: SiUnit): string {
    return `${PREFIX_OF_EXPONENT.get(exponent)}${base}${power > 1 ? SUPERSCRIPTS[power] : ''}`;
}

// The unit as displayed: 'um^2' -> 'µm²', other units as they are
export function displayUnitText(unit: string): string {
    const si = parseSiUnit(unit);
    return si ? siUnitText(si) : unit;
}

const plain = format(',~r');
const scientific = format('~e');

// Use scientific notation if very large / small
function numberFormat(values: readonly number[]): (v: number) => string {
    const maxAbs = max(values, (v) => (Number.isFinite(v) ? Math.abs(v) : NaN)) ?? 0;
    return maxAbs >= 1e6 || (maxAbs > 0 && maxAbs < 1e-3) ? scientific : plain;
}

export type DisplayScale = {
    unit: string;
    format: (v: number) => string;
};

// Align to the largest value
export function displayScale(unit: string, values: readonly number[]): DisplayScale {
    const si = parseSiUnit(unit);
    const maxAbs = max(values, (v) => (Number.isFinite(v) ? Math.abs(v) : NaN)) ?? 0;
    if (!si || maxAbs === 0) {
        return { unit: displayUnitText(unit), format: numberFormat(values) };
    }

    // The prefix that puts the largest value in [1, 1000^power)
    const steps = Math.floor(Math.log10(maxAbs) / (3 * si.power));
    const exponent = Math.min(30, Math.max(-30, si.exponent + 3 * steps));
    const factor = 10 ** ((si.exponent - exponent) * si.power);
    const scaled = values.map((v) => v * factor);
    const formatNumber = numberFormat(scaled);
    return { unit: siUnitText({ ...si, exponent }), format: (v) => formatNumber(v * factor) };
}

export function withUnit(text: string, unit: string): string {
    return unit ? `${text} ${unit}` : text;
}
