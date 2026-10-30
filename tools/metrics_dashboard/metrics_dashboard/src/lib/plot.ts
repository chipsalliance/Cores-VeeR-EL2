import * as Plot from '@observablehq/plot';
import * as d3 from 'd3';
import { valueTickFormat, withUnit, type Series, type ValueAxis, type XAxis, type XValue } from '#lib/metrics.ts';

// Plot's defaults (px)
const PLOT_FONT_SIZE = 10;
const PLOT_TICK_AREA = 30;
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
        xl: px('--ds-spacing-10'),
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

// Numeric X values get the same SI-prefixed ticks as the Y axis, unless the axis says otherwise
function xTickFormat<X extends XValue>(s: Series<X>, axis: XAxis<X>): ((x: X) => string) | undefined {
    if (axis.tickFormat || axis.scale !== 'linear') return axis.tickFormat;
    const format = valueTickFormat(s.data.map((d) => d.x as number));
    return (x) => format(x as number);
}

export function plot<X extends XValue>(s: Series<X>, axis: XAxis<X>, yAxis: ValueAxis): (SVGSVGElement | HTMLElement) & Plot.Plot {
    const tickFormat = xTickFormat(s, axis);
    const { sm, md, lineHeight } = aesirTokens();
    const xLabelOffset = PLOT_TICK_AREA + md;

    return Plot.plot({
        inset: md,
        marginLeft: marginLeft(
            s.data.map((d) => d.param),
            yAxis
        ),
        marginBottom: xLabelOffset + sm,

        x: {
            type: axis.scale,
            label: axis.label,
            labelOffset: xLabelOffset,
            tickFormat
        },

        y: {
            // Explicit ticks span the domain themselves
            nice: !yAxis.ticks,
            domain: yAxis.ticks && [yAxis.ticks[0], yAxis.ticks[yAxis.ticks.length - 1]],
            ticks: yAxis.ticks,
            label: yAxis.label,
            tickFormat: yAxis.format
        },

        marks: [
            Plot.gridX({ stroke: 'var(--ds-border)', strokeOpacity: 1 }),
            Plot.gridY({ stroke: 'var(--ds-border)', strokeOpacity: 1 }),

            axis.scale === 'point'
                ? null
                : Plot.lineY(s.data, {
                      x: 'x',
                      y: 'param',
                      stroke: 'var(--ds-accent)'
                  }),

            Plot.dot(s.data, {
                x: 'x',
                y: 'param',
                fill: 'var(--ds-accent)',

                tip: {
                    format: {
                        x: axis.tipFormat ?? tickFormat ?? true,
                        y: false,
                        Value: (v: number) => withUnit(yAxis.format(v), s.unit)
                    },

                    lineHeight,

                    channels: {
                        Value: 'param',
                        Category: 'category'
                    }
                }
            })
        ]
    });
}
