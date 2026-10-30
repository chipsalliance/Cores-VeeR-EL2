// Metrics: types, parsing, formatting, grouping, diff

import { format, max, timeFormat, timeParse } from 'd3';

// Types

export type Param = number | string | boolean | null | readonly Param[] | { readonly [key: string]: Param };

// Shapes produced by serialize_json.py, validated on the Python side

export type Config = {
    labels: Readonly<Record<string, string>>;
    units: Readonly<Record<string, string>>;
    date: string;
    commit: string;
    summary?: readonly string[];
    unplottable?: readonly string[];
};

export type RawMetric = {
    path: readonly string[];
    unit: string;
    // Indexed by run, null if the run lacks the metric
    values: readonly Param[];
};

export type RawNode = {
    ref: string;
    runs: readonly { id: number; source: string }[];
    metrics: readonly RawMetric[];
};

export type RawData = RawNode[];

// Numeric columns are packed, missing values are NaN
export type Column = { numeric: true; values: Float64Array } | { numeric: false; values: readonly Param[] };

export type Metric = {
    // Path joined with a SEPARATOR
    key: string;
    // Categories with a metric name at the end
    path: readonly string[];
    name: string;
    label: string;
    unit: string;
    column: Column;
};

export type Run = {
    // Index into the metric columns
    index: number;
    id: number;
    source: string;
    date: Date | null;
    commit: string | null;
    label: string;
    // Item value for dropdown
    value: string;
};

export type Dataset = {
    config: Config;
    // Newest first
    runs: Map<string, Run[]>;
    metrics: ReadonlyMap<string, Metric[]>;
    byKey: ReadonlyMap<string, ReadonlyMap<string, Metric>>;
};

export type XValue = number | string | Date;

export type XScale<X extends XValue> = X extends Date ? 'time' : X extends number ? 'linear' : 'point';

export type XAxis<X extends XValue = XValue> = {
    key: string;
    label: string;
    scale: XScale<X>;
    parse: (value: Param) => X | null;
    // Use Plot defaults if not specified
    tickFormat?: (x: X) => string;
    tipFormat?: (x: X) => string;
};

export type ValueAxis = {
    label: string;
    format: (v: number) => string;
    // Use Plot defaults if not specified
    ticks?: number[];
};

export type Point<X extends XValue = XValue> = {
    x: X;
    param: number;
    category: string;
};

export type Series<X extends XValue = XValue> = Metric & { data: Point<X>[] };

export type MetricDiff = {
    metric: Metric;
    base: number;
    target: number;
    percent: number | null;
};

export type Section<T> = {
    key: string;
    label: string;
    items: T[];
};

export type Group<T> = {
    name: string;
    label: string;
    sections: Section<T>[];
};

export type SummaryRow = {
    key: string;
    label: string;
    value: string;
};

// Dataset

export const SEPARATOR = '/';

export function labelOf(config: Config, name: string): string {
    return config.labels[name] ?? name;
}

function toColumn(values: readonly Param[]): Column {
    const numeric = values.every((v) => v === null || (typeof v === 'number' && Number.isFinite(v))) && values.some((v) => v !== null);
    return numeric ? { numeric: true, values: Float64Array.from(values, (v) => (v === null ? NaN : (v as number))) } : { numeric: false, values };
}

export function valueAt(metric: Metric, run: number): Param {
    const column = metric.column;
    if (!column.numeric) return column.values[run] ?? null;
    const value = column.values[run];
    return value === undefined || Number.isNaN(value) ? null : value;
}

export function numberAt(metric: Metric, run: number): number | null {
    const value = valueAt(metric, run);
    return typeof value === 'number' ? value : null;
}

export function buildDataset(raw: RawData, config: Config): Dataset {
    const metrics = new Map<string, Metric[]>(
        raw.map((it) => [
            it.ref,
            it.metrics.map(({ path, unit, values }) => {
                const name = path[path.length - 1];
                return { key: path.join(SEPARATOR), path, name, label: labelOf(config, name), unit, column: toColumn(values) };
            })
        ])
    );

    const byKey = new Map([...metrics].map(([ref, ms]) => [ref, new Map(ms.map((m) => [m.key, m]))]));

    const dates = new Map([...byKey].map(([ref, metrics]) => [ref, metrics.get(config.date)]));
    const commits = new Map([...byKey].map(([ref, metrics]) => [ref, metrics.get(config.commit)]));

    const runs = new Map(
        raw.map((it) => [
            it.ref,
            it.runs
                .map(({ id, source }, index) => {
                    const dateText = dates ? valueAt(dates.get(it.ref)!, index) : null;
                    const date = parseDate(dateText);
                    const commitValue = commits ? valueAt(commits.get(it.ref)!, index) : null;
                    const commit = commitValue === null ? null : String(commitValue);
                    return {
                        index,
                        id,
                        source,
                        date,
                        commit,
                        label: `${date ? String(dateText).trim() : `Run ${id}`} · ${commit ?? 'unknown'}`,
                        value: String(index)
                    };
                })
                .sort((a, b) => (b.date?.getTime() ?? -Infinity) - (a.date?.getTime() ?? -Infinity))
        ])
    );

    return { config, runs, metrics, byKey };
}

// Parsing / formatting

const parse = timeParse('%Y-%m-%d %H:%M');

export function parseDate(value: unknown): Date | null {
    return typeof value === 'string' ? parse(value.trim()) : null;
}

// Normalized to seconds in preprocessing
export const DURATION_UNIT = 's';

export function isDuration(unit: string): boolean {
    return unit === DURATION_UNIT;
}

export function formatDuration(seconds: number): string {
    const pad2 = (n: number) => String(n).padStart(2, '0');

    const sign = seconds < 0 ? '-' : '';
    const cs = Math.round(Math.abs(seconds) * 100);

    const hundredths = cs % 100;
    const secs = Math.floor(cs / 100) % 60;
    const minutes = Math.floor(cs / 6000) % 60;
    const hours = Math.floor(cs / 360000) % 24;
    const days = Math.floor(cs / 8640000);

    const fraction = hundredths ? `.${pad2(hundredths)}` : '';
    const clock = `${pad2(minutes)}:${pad2(secs)}${fraction}`;
    return days ? `${sign}${days}d ${pad2(hours)}:${clock}` : `${sign}${hours}:${clock}`;
}

export function durationTicks(values: readonly number[], count = 5): number[] {
    const min = 60;
    const hour = 60 * min;
    const day = 24 * hour;
    const week = 7 * day;

    // Tick steps that land on round durations: [unit, multipliers]
    const stepsByUnit: [number, number[]][] = [
        [1, [1, 2, 5, 10, 15, 30]],
        [min, [1, 2, 5, 10, 15, 30]],
        [hour, [1, 2, 3, 6, 12]],
        [day, [1, 2]],
        [week, [1]]
    ];

    const durationSteps = stepsByUnit.flatMap(([unit, multipliers]) => multipliers.map((m) => m * unit));

    const lo = Math.min(...values);
    const hi = Math.max(...values);
    if (!Number.isFinite(lo) || !Number.isFinite(hi)) return [];

    const span = hi - lo;
    const step = durationSteps.find((s) => span / s <= count) ?? Math.ceil(span / count / week) * week;
    // First tick at or below lo
    const first = Math.floor(lo / step) * step;
    // Last tick at or above hi
    const last = Math.max(Math.ceil(hi / step) * step, first + step);
    const ticks = [];
    for (let t = first; t <= last; t += step) ticks.push(t);
    return ticks;
}

// Use SI prefixes
export function valueTickFormat(values: readonly number[]): (v: number) => string {
    const maxAbs = max(values, Math.abs) ?? 0;
    return maxAbs >= 1e4 || (maxAbs > 0 && maxAbs < 1e-2) ? format('~s') : format(',~r');
}

export function displayUnit(unit: string): string {
    return isDuration(unit) ? '' : unit;
}

export function axisLabel({ label, unit }: Pick<Metric, 'label' | 'unit'>): string {
    if (isDuration(unit)) return `${label} [h:mm:ss]`;
    const u = displayUnit(unit);
    return u ? `${label} [${u}]` : label;
}

export function withUnit(text: string, unit: string): string {
    const u = displayUnit(unit);
    return u ? `${text} ${u}` : text;
}

export function formatValue(value: number, unit: string): string {
    return isDuration(unit) ? formatDuration(value) : withUnit(valueTickFormat([value])(value), unit);
}

export function formatParam(value: Param, unit: string): string {
    if (value === null) return '-';
    if (typeof value === 'number') return formatValue(value, unit);
    if (Array.isArray(value)) return value.map((v) => formatParam(v, unit)).join(', ');
    if (typeof value === 'object') return JSON.stringify(value);
    return String(value);
}

export function valueAxis(metric: Pick<Metric, 'label' | 'unit'>, values: readonly number[]): ValueAxis {
    const label = axisLabel(metric);
    return isDuration(metric.unit) ? { label, format: formatDuration, ticks: durationTicks(values) } : { label, format: valueTickFormat(values) };
}

const percent = format('+.2f');

export function formatPercent(value: number): string {
    return value === 0 ? '0%' : `${percent(value)}%`;
}

// X axis

export function dateAxis(key: string): XAxis<Date> {
    return {
        key,
        label: 'Run date',
        scale: 'time',
        parse: parseDate,
        tickFormat: timeFormat('%b %Y'),
        tipFormat: timeFormat('%Y-%m-%d %H:%M')
    };
}

export function numericAxis(metric: Metric): XAxis<number> {
    return {
        key: metric.key,
        label: axisLabel(metric),
        scale: 'linear',
        parse: (value) => (typeof value === 'number' && Number.isFinite(value) ? value : null)
    };
}

export function categoryAxis(metric: Metric): XAxis<string> {
    return {
        key: metric.key,
        label: metric.label,
        scale: 'point',
        parse: (value) => (typeof value === 'string' && value.trim() ? value.trim() : null)
    };
}

// Grouping

// Categories are separated with `/` - the last item is the actual metric
export function matchesEntry(metric: Metric, entry: string): boolean {
    return entry.includes(SEPARATOR) ? metric.key === entry || metric.key.startsWith(entry + SEPARATOR) : metric.path.includes(entry);
}

// Unplottable metrics are listed in the config
export function isPlottable(metric: Metric, config: Config): boolean {
    return metric.column.numeric && metric.key !== config.date && !(config.unplottable ?? []).some((entry) => matchesEntry(metric, entry));
}

export function categoryLabel(config: Config, categories: readonly string[]): string {
    return categories.map((c) => labelOf(config, c)).join(' > ');
}

export function groupByCategory<T>(items: readonly T[], pathOf: (item: T) => readonly string[], config: Config): Group<T>[] {
    const groups = new Map<string, Group<T> & { byKey: Map<string, Section<T>> }>();

    for (const item of items) {
        const path = pathOf(item);
        const [name, ...rest] = path.slice(0, -1);

        let group = groups.get(name);
        if (!group) groups.set(name, (group = { name, label: labelOf(config, name), sections: [], byKey: new Map() }));

        const key = rest.join(SEPARATOR);
        let section = group.byKey.get(key);
        if (!section) {
            section = { key, label: categoryLabel(config, rest), items: [] };
            group.byKey.set(key, section);
            group.sections.push(section);
        }
        section.items.push(item);
    }

    return [...groups.values()].map(({ name, label, sections }) => ({ name, label, sections }));
}

// Series

function isValidX(x: XValue | null): x is XValue {
    if (x === null) return false;
    if (x instanceof Date) return !isNaN(x.getTime());
    if (typeof x === 'number') return Number.isFinite(x);
    return true;
}

export function compareX(a: XValue, b: XValue): number {
    if (a instanceof Date && b instanceof Date) return a.getTime() - b.getTime();
    if (typeof a === 'number' && typeof b === 'number') return a - b;
    return String(a).localeCompare(String(b));
}

// Series of every plottable metric against the given X-axis, joined by run
export function seriesFor<X extends XValue>(ref: string, dataset: Dataset, axis: XAxis<X>): Series<X>[] | null {
    const xMetric = dataset.byKey.get(ref)!.get(axis.key);
    if (!xMetric) return null;

    const xs: [number, X][] = [];
    for (const run of dataset.runs.get(ref)!) {
        const value = valueAt(xMetric, run.index);
        const x = axis.parse(value);
        if (isValidX(x)) xs.push([run.index, x]);
        else console.warn(`Skipping run ${run.id}: cannot transform ${JSON.stringify(value)}`);
    }
    xs.sort((a, b) => compareX(a[1], b[1]));

    return dataset.metrics
        .get(ref)!
        .filter((m) => m.key !== axis.key && isPlottable(m, dataset.config))
        .map((metric) => {
            const category = categoryLabel(dataset.config, metric.path.slice(0, -1));
            const data = xs.flatMap(([run, x]) => {
                const param = numberAt(metric, run);
                return param === null ? [] : [{ x, param, category }];
            });
            return { ...metric, data };
        })
        .filter((s) => s.data.length > 0);
}

// Comparison

export function percentChange(base: number, target: number): number | null {
    if (base === 0) return target === 0 ? 0 : null;
    return ((target - base) / Math.abs(base)) * 100;
}

export function diffRuns(metrics: readonly Metric[], baseRun: number, targetRun: number): MetricDiff[] {
    return metrics.flatMap((metric) => {
        const base = numberAt(metric, baseRun);
        const target = numberAt(metric, targetRun);
        if (base === null || target === null) return [];
        return [{ metric, base, target, percent: percentChange(base, target) }];
    });
}

// Summary

export function summaryRows(ref: string, dataset: Dataset, run: number): SummaryRow[] {
    return (dataset.config.summary ?? []).flatMap((key) => {
        const metric = dataset.byKey.get(ref)!.get(key);
        if (!metric) return [];
        return [{ key, label: metric.label, value: formatParam(valueAt(metric, run), metric.unit) }];
    });
}
