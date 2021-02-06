set -ex && mkdir -p ../../build/release/bin
set -ex && docker create --name beldex-daemon-container beldex-daemon-image
set -ex && docker cp beldex-daemon-container:/usr/local/bin/ ../../build/
set -ex && docker rm beldex-daemon-container
