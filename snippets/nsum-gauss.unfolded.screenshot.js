#!/usr/bin/env node
const { cli } = require('./screenshot-lib.js');
// We used to have two copies of nsum-gauss and Qle-pairwise because this…
//   document.querySelectorAll('input[type="checkbox"]').forEach(function(toggle) {
//     toggle.checked = true; });
// …shows empty boxes instead of MathJax, but now we tweak visibility more carefully anyway.
cli({}, {
    width: '2.625in'
});
