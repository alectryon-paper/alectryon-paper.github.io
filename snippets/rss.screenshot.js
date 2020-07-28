#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');
cli({ script: () => {
    document.querySelectorAll('link').forEach(function(link) {
        link.parentNode.removeChild(link);
    });
}});
