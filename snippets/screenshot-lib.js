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

    await page.evaluateOnNewDocument(function() {
        window.runDelayed = f =>
            (window.delayed = window.delayed || []).push(f);
    });

    // console.log(src, dst);
    // https://github.com/puppeteer/puppeteer/issues/422, but this is not enough when a font isn't used until a later script (e.g. the bold font of hyp names)
    await page.goto('file://' + src, { waitUntil: 'networkidle2' });

    await page.evaluate(function() {
        const html = document.querySelector("html");
        const link = document.createElement("link");
        link.rel = "stylesheet";
        link.type = "text/css";
        link.href = "./screenshot.css";
        document.head.appendChild(link);
    });

    options.script && await page.evaluate(options.script);

    // Run delayed functions.  Some complex layouts can be influenced by the CSS
    // tweaks above (most notably the RBT example), so we need to delay the
    // layout until these CSS tweaks have been applied.
    await page.evaluate(function() {
        window.delayed && window.delayed.map(f => f());
    });

    // Make sure that any fonts needed by text revealed by `options.script` are
    // actually loaded.
    await page.evaluateHandle('document.fonts.ready');

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
