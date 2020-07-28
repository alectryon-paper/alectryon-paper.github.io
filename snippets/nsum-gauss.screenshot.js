#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');
// We have two copies of nsum-gauss and Qle-pairwise because this:
//   document.querySelectorAll('input[type="checkbox"]').forEach(function(toggle) {
//     toggle.checked = true; });
// Shows empty boxes instead of MathJax.
cli({});
