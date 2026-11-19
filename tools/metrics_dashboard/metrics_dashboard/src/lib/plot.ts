import * as Plot from '@observablehq/plot';
import * as d3 from 'd3';
import { type Series, type ValueAxis, type XAxis, type XValue } from '#lib/metrics.ts';
import { withUnit, displayScale } from '#lib/units.ts';

const PLOT_FONT_SIZE = 12;
const PLOT_TICK_AREA = 30 * (PLOT_FONT_SIZE / 10);
// Rough average glyph width of a tick label, in em
const CHAR_WIDTH_EM = 0.7;

// Read Aesir tokens for px values for d3 plots
let tokens: { sm: number; md: number; lg: number; xl: number; lineHeight: number } | undefined;

function aesirTokens() {
    const px = (token: string) => parseFloat(getComputedStyle(document.documentElement).getPropertyValue(token));
    return (tokens ??= {
        sm: px('--ds-spacing-1-5'),
        md: px('--ds-spacing-3'),
        lg: px('--ds-spacing-4'),
        xl: px('--ds-spacing-8'),
        lineHeight: px('--ds-font-line-height-xs') / px('--ds-font-size-xs')
    });
}

// Align left margin to the widest Y label
function marginLeft(values: readonly number[], { format: yFormat, ticks: yTicks }: ValueAxis) {
    const ticks =
        yTicks ??
        d3
            .scaleLinear()
            .domain(d3.extent(values) as [number, number])
            .nice()
            .ticks();

    const maxChars = d3.max(ticks, (t) => yFormat(t).length) ?? 0;
    const { lg, xl } = aesirTokens();

    return Math.max(xl, maxChars * CHAR_WIDTH_EM * PLOT_FONT_SIZE + lg);
}

function xTickFormat<X extends XValue>(s: Series<X>, axis: XAxis<X>): ((x: X) => string) | undefined {
    if (axis.tickFormat || axis.scale !== 'linear') return axis.tickFormat;
    const { format } = displayScale(
        '',
        s.data.map((d) => d.x as number)
    );
    return (x) => format(x as number);
}

export function plot<X extends XValue>(s: Series<X>, axis: XAxis<X>, yAxis: ValueAxis): (SVGSVGElement | HTMLElement) & Plot.Plot {
    const tickFormat = xTickFormat(s, axis);
    const { sm, md, xl, lineHeight } = aesirTokens();
    const xLabelOffset = PLOT_TICK_AREA + md;
    // One line per configuration, colored and with a legend if there's more than one
    const split = new Set(s.data.map((d) => d.configuration)).size > 1;
    const color = split ? 'configuration' : 'var(--ds-accent)';

    return Plot.plot({
        inset: md,
        marginLeft: marginLeft(
            s.data.map((d) => d.param),
            yAxis
        ),
        marginBottom: xLabelOffset + sm,
        marginTop: xl,

        x: {
            type: axis.scale,
            label: axis.label,
            labelOffset: xLabelOffset,
            tickSpacing: 80 * (PLOT_FONT_SIZE / 10), // 80 is Plot's default
            tickFormat
        },

        color: split ? { legend: true } : undefined,

        y: {
            // Explicit ticks span the domain themselves
            nice: !yAxis.ticks,
            domain: yAxis.ticks && [yAxis.ticks[0], yAxis.ticks[yAxis.ticks.length - 1]],
            ticks: yAxis.ticks,
            label: yAxis.label,
            tickFormat: yAxis.format
        },

        style: { fontSize: `${PLOT_FONT_SIZE}px` },
        marks: [
            Plot.gridX({ stroke: 'var(--ds-border)', strokeOpacity: 1 }),
            Plot.gridY({ stroke: 'var(--ds-border)', strokeOpacity: 1 }),

            axis.scale === 'point'
                ? null
                : Plot.lineY(s.data, {
                      x: 'x',
                      y: 'param',
                      z: 'configuration',
                      stroke: color
                  }),

            Plot.dot(s.data, {
                x: 'x',
                y: 'param',
                fill: color,

                tip: {
                    format: {
                        x: axis.tipFormat ?? tickFormat ?? true,
                        y: false,
                        Value: (v: number) => withUnit(yAxis.format(v), yAxis.unit)
                    },
                    fontSize: PLOT_FONT_SIZE,
                    lineHeight,

                    channels: {
                        Value: 'param',
                        Category: 'category',
                        ...(split ? { Configuration: 'configuration' } : {})
                    }
                }
            })
        ]
    });
}
