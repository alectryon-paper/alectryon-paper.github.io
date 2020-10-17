#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');
cli({
    script: () => {
        document.querySelectorAll("pre").forEach(pre => {
            pre.style.fontFamily = "'Iosevka'"
        });
    }
}, {
    // width: '3in',
});
