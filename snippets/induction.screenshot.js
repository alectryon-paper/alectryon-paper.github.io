#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');
cli({ script: () => {
    document.querySelectorAll('.coq-extra-goal-toggle').forEach(function(toggle) {
        toggle.checked = true; });
}});
