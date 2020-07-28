#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');
cli({ script: () => {
    document.querySelectorAll('.topic').forEach(function(topic) {
        topic.style.padding = 0;
        topic.style.border = 'none';
    });
}});
