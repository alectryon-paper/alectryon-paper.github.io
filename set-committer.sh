#!/usr/bin/env sh
git config --local user.name "Anonymous"
git config --local user.email "anonymous@example.com"

if false; then
    git config --unset user.name
    git config --unset user.email

    FILTER_BRANCH_SQUELCH_WARNING=1 git filter-branch --env-filter "
export GIT_COMMITTER_NAME='$(git config user.name)'
export GIT_COMMITTER_EMAIL='$(git config user.email)'
export GIT_AUTHOR_NAME='$(git config user.name)'
export GIT_AUTHOR_EMAIL='$(git config user.email)'
" --tag-name-filter cat -- --branches --tags
fi
