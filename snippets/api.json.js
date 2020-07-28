#!/usr/bin/env node
const fs = require('fs');
const util = require('util');

fs.writeFileSync(
    "api.json",
    util.inspect(JSON.parse(fs.readFileSync("api.json")), {
        depth: null,
        colors: false,
        breakLength: 45
    })
);
