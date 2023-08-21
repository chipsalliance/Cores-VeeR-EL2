({{ ref }})=
# Coverage dashboard

## Summary reports (all tests)

{%- for coverage in summary %}
{%- if summary[coverage] %}
 * [{{ coverage }} coverage](external:coverage_dashboard/{{ summary[coverage] }}/index.html)
{%- else %}
 * {{ coverage }} coverage (no data)
{%- endif %}
{%- endfor %}

## Individual test reports

{%- for coverage in individual %}
### {{ coverage }} coverage
{%- if individual[coverage] %}
{%- for test in individual[coverage] %}
 * [{{ test }}](external:coverage_dashboard/{{ individual[coverage][test] }}/index.html)
{%- endfor %}
{%- else %}
no data
{%- endif %}
{%- endfor %}
