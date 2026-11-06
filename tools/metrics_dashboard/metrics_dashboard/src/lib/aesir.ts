// Aligns columns across multiple tables (calculates the max width of it's contents)
export function alignColumns(node: HTMLElement) {
    let frame = 0;

    function sync() {
        const tables = [...node.querySelectorAll('table')];
        if (!tables.length) return;

        const headerCells = tables.flatMap((t) => [...(t.tHead?.rows[0]?.cells ?? [])]);
        headerCells.forEach((c) => (c.style.width = ''));

        node.classList.add('measuring');
        const max: number[] = [];
        for (const table of tables) {
            for (const row of table.rows) {
                [...row.cells].forEach((cell, i) => {
                    if (cell.colSpan > 1) return;
                    max[i] = Math.max(max[i] ?? 0, cell.getBoundingClientRect().width);
                });
            }
        }
        node.classList.remove('measuring');

        for (const table of tables) {
            [...(table.tHead?.rows[0]?.cells ?? [])].forEach((c, i) => {
                if (max[i]) c.style.width = `${Math.ceil(max[i])}px`;
            });
        }
    }

    const schedule = () => {
        cancelAnimationFrame(frame);
        frame = requestAnimationFrame(sync);
    };

    const observer = new MutationObserver(schedule);
    observer.observe(node, { childList: true, subtree: true });
    document.fonts.ready.then(schedule);
    schedule();

    return {
        destroy() {
            observer.disconnect();
            cancelAnimationFrame(frame);
        }
    };
}
