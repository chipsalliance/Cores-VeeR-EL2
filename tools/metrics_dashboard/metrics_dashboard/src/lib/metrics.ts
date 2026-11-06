// Metrics: types, parsing, formatting, grouping, diff

import { format, timeFormat, timeParse } from 'd3';
import { displayScale, displayUnitText, withUnit } from '#lib/units.ts';

// Types

export type Param = number | string | boolean | null | readonly Param[] | { readonly [key: string]: Param };

// Shapes produced by serialize_json.py, validated on the Python side

export type Config = {
    labels: Readonly<Record<string, string>>;
    // Display units of metadata fields ('@...')
    units?: Readonly<Record<string, string>>;
    summary?: readonly string[];
    // Shown on the overview cards
    overview?: readonly string[];
    unplottable?: readonly string[];
};

// Metrics definitions (paths and units)
export type RawMetric = {
    path: readonly string[];
    unit: string;
};

export type Metadata = {
    readonly date: string;
    readonly current_commit: string;
    readonly is_pr: boolean;
    readonly source_branch: string;
    readonly source_repository: string;
    readonly pr_number?: number;
    readonly pr_title?: string;
    // Link to the run
    readonly url?: string;
    readonly target_repository?: string;
    readonly pipeline_status?: PipelineStatus;
    readonly [key: string]: Param | undefined;
};

export type PipelineStatus = 'passed' | 'passed_with_warnings' | 'failed' | 'canceled';

export type RawRun = {
    id: number;
    metadata: Metadata;
};

// A tracked branch or PR
export type Ref = { kind: 'branch'; name: string } | { kind: 'pr'; number: number };

export type RawRef = Ref & {
    runs: readonly RawRun[];
    values: readonly (readonly Param[] | null)[];
};

export type RawData = {
    metrics: readonly RawMetric[];
    refs: readonly RawRef[];
};

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
    metadata: Metadata;
    date: Date | null;
    commit: string;
    label: string;
    // Item value for dropdown
    value: string;
};

export type Dataset = {
    config: Config;
    // Keyed by refKey()
    refs: readonly (Ref & { key: string })[];
    // Newest first
    runs: Map<string, Run[]>;
    metrics: ReadonlyMap<string, Metric[]>;
    byKey: ReadonlyMap<string, ReadonlyMap<string, Metric>>;
};

export type XValue = number | string | Date;

export type XScale<X extends XValue> = X extends Date ? 'time' : X extends number ? 'linear' : 'point';

export type XAxis<X extends XValue = XValue> = {
    // Metric used as the X axis (excluded from the series), if any
    key?: string;
    label: string;
    scale: XScale<X>;
    // X value of the run, null if the run can't be placed on the axis
    x: (run: Run) => X | null;
    // Use Plot defaults if not specified
    tickFormat?: (x: X) => string;
    tipFormat?: (x: X) => string;
};

export type ValueAxis = {
    label: string;
    unit: string;
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

export const SEPARATOR = '.';
// References a metadata field instead of a metric, e.g. '@pr_title' (nested: '@a.b')
export const METADATA_PREFIX = '@';

export function isMetadataRef(key: string): boolean {
    return key.startsWith(METADATA_PREFIX);
}

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

// Key of a ref in the dataset's maps
export function refKey(ref: Ref): string {
    return ref.kind === 'pr' ? `pr/${ref.number}` : `branch/${ref.name}`;
}

// The main branch (default across the views)
export const MAIN_REF = refKey({ kind: 'branch', name: 'main' });

export function buildDataset(raw: RawData, config: Config): Dataset {
    const refs = raw.refs.map((r) => {
        const ref: Ref = r.kind === 'pr' ? { kind: 'pr', number: r.number } : { kind: 'branch', name: r.name };
        return { ...ref, key: refKey(ref) };
    });

    const metrics = new Map<string, Metric[]>(
        raw.refs.map((it, i) => [
            refs[i].key,
            raw.metrics.flatMap(({ path, unit }, m) => {
                const values = it.values[m];
                if (!values) return [];
                const name = path[path.length - 1];
                return [{ key: path.join(SEPARATOR), path, name, label: labelOf(config, name), unit, column: toColumn(values) }];
            })
        ])
    );

    const byKey = new Map([...metrics].map(([ref, ms]) => [ref, new Map(ms.map((m) => [m.key, m]))]));

    const runs = new Map(
        raw.refs.map((it, i) => [
            refs[i].key,
            it.runs
                .map(({ id, metadata }, index) => {
                    const date = parseDate(metadata.date);
                    const commit = metadata.current_commit;
                    return {
                        index,
                        id,
                        metadata,
                        date,
                        commit,
                        label: `${date ? metadata.date.trim() : `Run ${id}`} · ${commit}`,
                        value: String(index)
                    };
                })
                .sort((a, b) => (b.date?.getTime() ?? -Infinity) - (a.date?.getTime() ?? -Infinity))
        ])
    );

    return { config, refs, runs, metrics, byKey };
}

// Parsing / formatting

export function parseDate(value: unknown): Date | null {
    const parse = timeParse('%Y-%m-%d %H:%M');
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

export function displayUnit(unit: string): string {
    return isDuration(unit) ? '' : displayUnitText(unit);
}

export function axisLabel({ label, unit }: Pick<Metric, 'label' | 'unit'>): string {
    if (isDuration(unit)) return `${label} [h:mm:ss]`;
    const u = displayUnit(unit);
    return u ? `${label} [${u}]` : label;
}

// Values sharing one display unit (e.g. a row of a comparison), SI units get the prefix that suits the largest
export function formatValues(values: readonly number[], unit: string): string[] {
    if (isDuration(unit)) return values.map(formatDuration);
    const scale = displayScale(unit, values);
    return values.map((v) => withUnit(scale.format(v), scale.unit));
}

export function formatValue(value: number, unit: string): string {
    return formatValues([value], unit)[0];
}

export function formatParam(value: Param, unit: string): string {
    if (value === null) return '-';
    if (typeof value === 'number') return formatValue(value, unit);
    if (Array.isArray(value)) return value.map((v) => formatParam(v, unit)).join(', ');
    if (typeof value === 'object') return JSON.stringify(value);
    return String(value);
}

export function valueAxis(metric: Pick<Metric, 'label' | 'unit'>, values: readonly number[]): ValueAxis {
    if (isDuration(metric.unit)) return { label: axisLabel(metric), unit: '', format: formatDuration, ticks: durationTicks(values) };
    const scale = displayScale(metric.unit, values);
    return { label: scale.unit ? `${metric.label} [${scale.unit}]` : metric.label, unit: scale.unit, format: scale.format };
}

export function formatDiff(base: number, target: number): string {
    const diffFmt = format('+.2~f');
    const raw = target - base;
    const pct = base === 0 ? 0 : (raw / Math.abs(base)) * 100;
    // d3 uses '−' for formatting - keep for consistency
    return raw === 0 ? '−' : `${diffFmt(raw)} (${diffFmt(pct)}%)`;
}

// X axis

export function dateAxis(): XAxis<Date> {
    return {
        label: 'Run date',
        scale: 'time',
        x: (run) => run.date,
        tickFormat: timeFormat('%b %Y'),
        tipFormat: timeFormat('%Y-%m-%d %H:%M')
    };
}

export function numericAxis(metric: Metric): XAxis<number> {
    return {
        key: metric.key,
        label: axisLabel(metric),
        scale: 'linear',
        x: (run) => numberAt(metric, run.index)
    };
}

export function categoryAxis(metric: Metric): XAxis<string> {
    return {
        key: metric.key,
        label: metric.label,
        scale: 'point',
        x: (run) => {
            const value = valueAt(metric, run.index);
            return typeof value === 'string' && value.trim() ? value.trim() : null;
        }
    };
}

// Grouping

// Categories are separated with SEPARATOR - the last item is the actual metric
export function matchesEntry(metric: Metric, entry: string): boolean {
    return entry.includes(SEPARATOR) ? metric.key === entry || metric.key.startsWith(entry + SEPARATOR) : metric.path.includes(entry);
}

// Unplottable metrics are listed in the config (metadata is never plotted)
export function isPlottable(metric: Metric, config: Config): boolean {
    return metric.column.numeric && !(config.unplottable ?? []).some((entry) => matchesEntry(metric, entry));
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
    const runs = dataset.runs.get(ref);
    if (!runs || (axis.key !== undefined && !dataset.byKey.get(ref)?.has(axis.key))) return null;

    const xs: [number, X][] = [];
    for (const run of runs) {
        const x = axis.x(run);
        if (isValidX(x)) xs.push([run.index, x]);
        else console.warn(`Skipping run ${run.id}: no valid '${axis.label}' value`);
    }
    xs.sort((a, b) => compareX(a[1], b[1]));

    return (dataset.metrics.get(ref) ?? [])
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
        return [{ metric, base, target }];
    });
}

// Lookup

// Metadata field referenced as '@name' or '@a.b', undefined if not reported by the run
export function metadataValue(metadata: Metadata, key: string): Param | undefined {
    type Node = Param | undefined | { readonly [key: string]: Param | undefined };
    let value: Node = metadata;
    for (const name of key.slice(METADATA_PREFIX.length).split(SEPARATOR)) {
        if (value === null || typeof value !== 'object' || Array.isArray(value)) return undefined;
        value = (value as { readonly [key: string]: Param | undefined })[name];
    }
    return value as Param | undefined;
}

export type Resolved = { label: string; unit: string; value: Param };

// Resolves a metric path or a metadata reference ('@...') for the run, undefined if unknown
export function resolve(dataset: Dataset, ref: string, run: Run, key: string): Resolved | undefined {
    if (isMetadataRef(key)) {
        const value = metadataValue(run.metadata, key);
        // Display unit only, metadata values are not converted
        const unit = dataset.config.units?.[key] ?? '';
        return value === undefined ? undefined : { label: keyLabel(dataset.config, key), unit, value };
    }
    const metric = dataset.byKey.get(ref)?.get(key);
    return metric && { label: metric.label, unit: metric.unit, value: valueAt(metric, run.index) };
}

// Summary

// Label of a metric path or a metadata reference ('@...')
function keyLabel(config: Config, key: string): string {
    const name = key.slice(key.lastIndexOf(SEPARATOR) + 1).replace(METADATA_PREFIX, '');
    return (isMetadataRef(key) && config.labels[key]) || labelOf(config, name);
}

// Rows of metric paths / metadata references (summary, overview)
export function summaryRows(ref: string, dataset: Dataset, run: Run, keys: readonly string[] = [], keepMissing = false): SummaryRow[] {
    return keys.flatMap((key) => {
        const resolved = resolve(dataset, ref, run, key);
        if (resolved) return [{ key, label: resolved.label, value: formatParam(resolved.value, resolved.unit) }];
        return keepMissing ? [{ key, label: keyLabel(dataset.config, key), value: '-' }] : [];
    });
}

// Overview

export type Badge = { variant: 'success' | 'warning' | 'destructive' | 'secondary' | 'outline'; label: string };

const PIPELINE_BADGES: Record<PipelineStatus, Badge> = {
    passed: { variant: 'success', label: 'passed' },
    passed_with_warnings: { variant: 'warning', label: 'passed with warnings' },
    failed: { variant: 'destructive', label: 'failed' },
    canceled: { variant: 'secondary', label: 'canceled' }
};

export function pipelineBadge(status: PipelineStatus | undefined): Badge {
    return (status && PIPELINE_BADGES[status]) || { variant: 'outline', label: 'unknown' };
}

export type OverviewCard = {
    key: string;
    title: string;
    // PR title, none for branches
    description?: string;
    url?: string;
    badge: Badge;
    // Date reported by the latest run
    updated: string;
    rows: SummaryRow[];
};

// Branches first (main, then by name), then PRs from the most recently updated
function compareRefs(dataset: Dataset, a: Ref & { key: string }, b: Ref & { key: string }): number {
    if (a.kind !== b.kind) return a.kind === 'branch' ? -1 : 1;
    if (a.kind === 'branch' && b.kind === 'branch') {
        if (a.key === MAIN_REF || b.key === MAIN_REF) return a.key === MAIN_REF ? -1 : 1;
        return a.name.localeCompare(b.name);
    }
    const time = (ref: string) => dataset.runs.get(ref)?.[0]?.date?.getTime() ?? -Infinity;
    return time(b.key) - time(a.key) || (b as { number: number }).number - (a as { number: number }).number;
}

export function overviewCards(dataset: Dataset): OverviewCard[] {
    return [...dataset.refs]
        .sort((a, b) => compareRefs(dataset, a, b))
        .flatMap((ref) => {
            const latest = dataset.runs.get(ref.key)?.[0];
            if (!latest) return [];
            const { metadata } = latest;
            return [
                {
                    key: ref.key,
                    title: ref.kind === 'pr' ? `PR #${ref.number}` : ref.name,
                    description: ref.kind === 'pr' ? metadata.pr_title : undefined,
                    url: metadata.url,
                    badge: pipelineBadge(metadata.pipeline_status),
                    updated: metadata.date,
                    rows: summaryRows(ref.key, dataset, latest, dataset.config.overview, true)
                }
            ];
        });
}

// Value of a latest-reported metric (path) or a metadata field
export function latestValue(dataset: Dataset, ref: string, key: string): Param {
    const newest = dataset.runs.get(ref)?.[0];
    return (newest && resolve(dataset, ref, newest, key)?.value) ?? null;
}
