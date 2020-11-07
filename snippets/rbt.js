function draw(container, data) {
    container = d3.select(container);

    const node = container.append('span');
    node.node().className = "rbt-graph";

    const svg = node.append('svg');
    const inner = svg.append('g');

    const DIM = 7;
    var g = new dagreD3.graphlib.Graph().setGraph({rankdir: 'TB', edgesep: DIM, ranksep: DIM, nodesep: DIM});

    const EDGE_STYLES = { node: "stroke: #2e3436; stroke-width: 1.5; fill: none;", leaf: "visibility: hidden;" };
    const EDGE_PROPS = kind => ({ style: EDGE_STYLES[kind], curve: d3.curveBasis, arrowheadStyle: "fill: none;" });

    const NODE_STYLES = { Black: "fill: #2e3436", Red: "fill: #cc0000;" };
    const NODE_PROPS = color => ({ style: NODE_STYLES[color], shape: "circle", labelStyle: "fill: #eeeeec; font-size: 18px;", width: DIM, height: DIM });
    const INVISIBLE_NODE_PROPS = { style: "visibility: hidden;" };

    var gensym = 0;
    var dfs = tree => {
        const id = 'node' + (gensym++);

        if (tree.kind === "node") {
            var label = d3.select(document.createElementNS('http://www.w3.org/2000/svg', 'text'));
            label.append("tspan")
                .attr('x', '0')
                .attr('dy', '1em')
                .text(tree.value);
            g.setNode(id, { label: label.node(), labelType: "svg", ...NODE_PROPS(tree.color) });;
            if (tree.left.kind == "node" || tree.right.kind == "node") {
                const left = dfs(tree.left), right = dfs(tree.right);
                g.setEdge(id, left, EDGE_PROPS(tree.left.kind));
                g.setEdge(id, right, EDGE_PROPS(tree.right.kind));
            }
            return id;
        }

        g.setNode(id, { label: "", ...INVISIBLE_NODE_PROPS });;
        return id;
    }

    dfs(data.tree);

    // Set up zoom support
    var zoom = d3.zoom().on("zoom", function() {
        inner.attr("transform", d3.event.transform);
    });
    svg.call(zoom);

    // Create the renderer
    var render = new dagreD3.render();

    // Run the renderer. This is what draws the final graph.
    render(inner, g);

    // Scale the graph relative to the reference font size (16px)
    svg.attr('height', "8.5em");
    svg.attr("width", "8.5em");

    var { height, width } = svg.node().getBoundingClientRect();
    var scale = height / (16 * 8.5) * 1; // 16px * svg.attr('height') 
    
    const threshold = 0.5;
    if (g.graph().height < threshold * height / scale) {
        svg.attr("height", threshold * height);
    }
    
    const scaled_offset = (width - g.graph().width * scale) / 2;
    svg.call(zoom.transform, d3.zoomIdentity.translate(scaled_offset, 0).scale(scale));
}

function prettify_messages() {
    document.querySelectorAll(".coq-message").forEach(msg => {
        try {
            const m = msg.innerText.match(/^(=\s*)([\s\S]*)(:[\s\S]*)$/);
            const data_str = m[2].replace(/;/g, ",").replace(/'/g, '"');
            const data = JSON.parse(data_str);

            const _msg = msg.cloneNode(false);
            msg.parentNode.replaceChild(_msg, msg);

            const wrapper = document.createElement("span");
            wrapper.className = "rbt-wrapper";

            if (Array.isArray(data)) {
                _msg.appendChild(document.createTextNode(m[1] + "["));
                _msg.appendChild(wrapper);
                _msg.appendChild(document.createTextNode("]"));

                const sequence = document.createElement("span");
                sequence.className = "rbt-sequence";
                wrapper.appendChild(sequence);

                data.forEach(graph => draw(sequence, graph));
            } else {
                _msg.appendChild(wrapper);
                draw(wrapper, data);
            }

            _msg.appendChild(document.createElement("wbr"));
            const annot = document.createElement("span");
            annot.appendChild(document.createTextNode(m[3]));
            annot.className = "conway-annot";
            _msg.appendChild(annot);

        } catch (err) {
            console.log(err);
        }
    }
    );
}

(window.runDelayed || (f => f()))(prettify_messages);
