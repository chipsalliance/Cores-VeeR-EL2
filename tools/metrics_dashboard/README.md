# Metrics dashboard

Self-contained single page application for metrics visualization.

## Data preparation

Metric data needs to be serialized and normalized prior to being provided for the dashboard.

The metrics are expected to be in the JSON format and fulfill the metrics (`tools/metrics.schema.json`) and configuration (`tools/config.schema.json`) schemas.

To normalize and serialize metric files run `serialize_json.py` script:

```
tools/serialize_json.py -o metrics_dashboard/src/lib/data/ -i sample-data/metrics* -c sample-data/config.json
```

### Validation

You may separately validate the metrics and the configuration file using the python `validate_metrics.py` script:

```
validate_metrics.py [-h] [--metrics_schema METRICS_SCHEMA] [--config CONFIG] [--config-schema CONFIG_SCHEMA]
```

## Building the dashboard

```sh
cd metrics_dashboard
git submodule update --init  # Dashboard uses component library submodule
npm i  # install project npm dependencies
npm run build  # invoke static page build
```

The output is written to `build/`. Preview it with `npm run preview` or simply opening the `build/index.html` file in the browser of choice.

## Development

The app can be build with the server that allows for live preview of performed changes:

```sh
npm i  # install project npm dependencies
npm run dev  # Run development server
```

This will start the development server and log the the URL where the server can be accessed.

### Checks

Dashboard utilizes typescript and external linter, one can perform checks with:

```sh
npm run check   # svelte-check (types)
npm run lint    # prettier + eslint
npm test        # vitest (unit tests)
```
