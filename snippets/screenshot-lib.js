const puppeteer = require('puppeteer-core');
const path = require('path');

const firefoxOptions = {
  product: 'firefox',
  extraPrefsFirefox: {
    // Enable additional Firefox logging from its protocol implementation
    'remote.log.level': 'Trace',
  },
  // Make browser logs visible
  dumpio: true,
};

async function screenshot(src, dst, options={}, pdfOptions={}, launchOptions={}) {
    const browser = await puppeteer.launch({
        executablePath: "google-chrome",
        ...launchOptions
    });
    // console.log(await browser.version());

    const page = await browser.newPage();
    page.emulateMediaType('screen');

    // console.log(src, dst);
    await page.goto('file://' + src, { waitUntil: 'networkidle2'});

    await page.evaluate(function() {
        const html = document.querySelector("html");
        html.style.fontSize = "10px";
        html.style.margin = 0;
        html.style.fontFamily = "unset";

        font_css = `
.docutils.literal {
    font-family: 'Iosevka Slab Web', 'Iosevka Web', 'Iosevka Slab', 'Iosevka', 'Fira Code', monospace;
    font-feature-settings: "XV00" 1; /* Use Coq ligatures when Iosevka is available */
    line-height: initial;
}
`;
        const styleSheet = document.createElement("style");
        styleSheet.type = "text/css";
        styleSheet.innerText = font_css;
        document.head.appendChild(styleSheet);

        const body = document.querySelector("body");
        body.style.margin = 0;

        document.querySelectorAll("pre").forEach((pre) => {
            pre.style.lineHeight = 1.15;
        });

        const root = document.querySelector(".alectryon-standalone");
        // root.style.fontFamily = "'Linux Libertine', 'Linux Libertine O'";

        document.querySelectorAll(".alectryon-header").forEach((header) => {
            header.style.display = "none";
        });

        document.querySelectorAll("h1").forEach((h1) => {
            h1.style.marginBottom = 0;
        });
    });
    options.script && await page.evaluate(options.script);

    await page.pdf({ path: dst, printBackground: true,
                     width: '3.3in', ...pdfOptions });

    await browser.close();
}

async function cli(...args) {
    const fsrc = path.resolve(process.argv[2]);
    const fdst = path.resolve(process.argv[3]);
    screenshot(fsrc, fdst, ...args);
}

exports.cli = cli;
