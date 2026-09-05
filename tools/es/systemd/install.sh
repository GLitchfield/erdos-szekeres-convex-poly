#!/usr/bin/env bash
# Install and enable the nightly timer for the current user (WSL: needs systemd user sessions).
set -e
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p ~/.config/systemd/user ~/.es/erdos-szekeres/logs
cp "$here/es-nightly.service" "$here/es-nightly.timer" ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now es-nightly.timer
systemctl --user list-timers es-nightly.timer --no-pager
