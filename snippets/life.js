function draw(data) {
    const INNER_SIZE = 60;
    const EDGE_WIDTH = 1;

    const BLOCK_COUNT = data.length;
    const EDGE_COUNT = BLOCK_COUNT + 1;
    const OUTER_SIZE = INNER_SIZE + EDGE_WIDTH * EDGE_COUNT;
    const BLOCK_INNER_SIZE = INNER_SIZE / BLOCK_COUNT;
    const CELL_SIZE = BLOCK_INNER_SIZE * 0.8;
    const BLOCK_OUTER_SIZE = BLOCK_INNER_SIZE + EDGE_WIDTH;

    const CELL_FILL = { color: "black" };
    const EDGE_STROKE = { color: "#888a85", width: EDGE_WIDTH };

    var svg = SVG();
    svg.viewbox(0, 0, OUTER_SIZE, OUTER_SIZE);
    // svg.attr({ width: BLOCK_COUNT * 20 + EDGE_COUNT * EDGE_WIDTH,
    //            height:  BLOCK_COUNT * 20 + EDGE_COUNT * EDGE_WIDTH });
    svg.attr({ width: OUTER_SIZE,
               height:  OUTER_SIZE });
    svg.rect(OUTER_SIZE, OUTER_SIZE).fill("white");

    for (var bid = 0; bid <= BLOCK_COUNT; bid++) {
        const offset = bid * BLOCK_OUTER_SIZE + EDGE_WIDTH / 2;
        var horizontal = svg.line(0, 0, OUTER_SIZE, 0).move(0, offset);
        var vertical = svg.line(0, 0, 0, OUTER_SIZE).move(offset, 0);
        horizontal.stroke(EDGE_STROKE);
        vertical.stroke(EDGE_STROKE);
    }

    for (var x = 0; x < BLOCK_COUNT; x++) {
        for (y = 0; y < BLOCK_COUNT; y++) {
            if (data[y][x] == 1) {
                const vx = x * BLOCK_OUTER_SIZE + EDGE_WIDTH + BLOCK_INNER_SIZE / 2;
                const vy = y * BLOCK_OUTER_SIZE + EDGE_WIDTH + BLOCK_INNER_SIZE / 2;
                svg.circle(CELL_SIZE).center(vx, vy).fill(CELL_FILL);
            }
        }
    }

    return svg;
}

function prettify_messages() {
    document.querySelectorAll(".coq-message").forEach(msg => {
        try {
            const m = msg.innerText.match(/^(=\s*)([\s\S]*)(:[\s\S]*)$/);
            const data_str = m[2].replace(/;/g, ",");
            const data = JSON.parse(data_str);
            const svgs = data.map(draw);

            const wrapper = document.createElement("span");
            wrapper.className = "conway-wrapper";

            const sequence = document.createElement("span");
            sequence.className = "conway-sequence";
            svgs.forEach((svg, i) => {
                const sp = document.createElement("span");
                sp.className = "conway-snapshot";
                sequence.appendChild(sp);
                svg.addTo(sp);
            });
            wrapper.appendChild(sequence);

            const _msg = msg.cloneNode(false);
            _msg.appendChild(document.createTextNode(m[1] + "["));
            _msg.appendChild(wrapper);
            _msg.appendChild(document.createTextNode("]"));
            _msg.appendChild(document.createElement("wbr"));

            const annot = document.createElement("span");
            annot.appendChild(document.createTextNode(m[3]));
            annot.className = "conway-annot";
            _msg.appendChild(annot);

            msg.parentNode.replaceChild(_msg, msg);
        } catch (err) {
            console.log(err);
        }
    });
}

prettify_messages();
