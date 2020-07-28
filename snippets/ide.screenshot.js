#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');

cli({
    script: () => {
        Alectryon.styles.setStyle('windowed');
        Alectryon.slideshow.navigate(7);

        const progress_bar = `
.alectryon-root.alectryon-standalone.alectryon-windowed:after,
.alectryon-root.alectryon-standalone.alectryon-windowed:before {
  content: "";
  position: absolute;
}

.alectryon-root.alectryon-standalone.alectryon-windowed:after {
  top: 9pt;
  right: 3pt;
  width: 2pt;
  height: 35%;
  border-radius: 1pt;
  background: #555;
}

.alectryon-root.alectryon-standalone.alectryon-windowed:before {
  top: 8pt;
  bottom: 2pt;
  right: 2pt;
  width: 4pt;
  border-radius: 4pt;
  background: #ddd;
}
`;

        const styleSheet = document.createElement("style");
        styleSheet.type = "text/css";
        styleSheet.innerText = progress_bar;
        document.head.appendChild(styleSheet);

        const root = document.querySelector(".alectryon-standalone.alectryon-windowed");
        root.style.padding = "0";

        const outputs = document.querySelectorAll(".coq-output");
        outputs.forEach((out) => {
            out.style.paddingLeft = out.style.paddingRight = 0;
        });
    },
}, {
    height: '2.23in'
});
