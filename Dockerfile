# Stage 1: Builder
FROM debian:stable-slim AS builder

ENV DEBIAN_FRONTEND=noninteractive

# 1. Install Build Tools
RUN apt-get update && apt-get install -y --no-install-recommends \
    git gcc make luarocks unzip build-essential ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

# 2. Build LuaJIT (Lua 5.2 compatibility)
RUN git clone https://github.com/LuaJIT/LuaJIT.git /tmp/luajit && \
    cd /tmp/luajit && \
    make XCFLAGS="-DLUAJIT_ENABLE_LUA52COMPAT" && \
    make install && \
    cd / && rm -rf /tmp/luajit

# 3. Install Lua Dependencies & Patch smiti18n
RUN luarocks install utf8 && \
    luarocks install smiti18n && \
    mkdir -p /usr/local/share/lua/5.1/smiti18n && \
    echo 'return "1.0.0"' > /usr/local/share/lua/5.1/smiti18n/version.lua

# 3b. Build lpeg 1.1.0 from source with the firstcap patch (upstream bug:
# the match-time CapState leaves firstcap uninitialized, so an accumulator
# capture nested in a Cmt reads stack garbage — crashes on newer LuaJIT).
COPY patches/lpeg-1.1.0-firstcap.patch /tmp/lpeg-firstcap.patch
RUN curl -sSL https://www.inf.puc-rio.br/~roberto/lpeg/lpeg-1.1.0.tar.gz | tar -xz -C /tmp && \
    cd /tmp/lpeg-1.1.0 && git apply /tmp/lpeg-firstcap.patch && \
    mkdir -p /usr/local/lib/lua/5.1 && \
    gcc -O2 -fPIC -shared -o /usr/local/lib/lua/5.1/lpeg.so \
        lpvm.c lptree.c lpcap.c lpcode.c lpcset.c lpprint.c \
        -I/usr/local/include/luajit-2.1 && \
    rm -rf /tmp/lpeg-1.1.0 /tmp/lpeg-firstcap.patch

# 4. SURGERY: Create staging area
RUN mkdir -p /tmp/out/usr/bin /tmp/out/usr/lib /tmp/out/usr/local /tmp/out/lib

# Copy application files
RUN cp -a /usr/local /tmp/out/usr/

# 5. Trace and copy ONLY necessary shared libraries
RUN list="$(ldd /usr/local/bin/luajit | grep "=> /" | awk '{print $3}')" && \
    for i in $list; do \
        basename=$(basename "$i"); \
        case "$basename" in \
            libc.so.*|libstdc++.so.*|libgcc_s.so.*|libm.so.*|libdl.so.*|libpthread.so.*|libz.so.*|libssl.so.*|libcrypto.so.*|ld-*.so.*|libgomp.so.*|libzstd.so.*|librt.so.*|libnsl.so.*) \
                continue ;; \
        esac; \
        dir=$(dirname "$i"); \
        mkdir -p "/tmp/out$dir"; \
        cp -L "$i" "/tmp/out$i"; \
    done

# 6. Strip binaries and shared objects
RUN find /tmp/out -type f \( -name "*.so" -o -executable \) -exec strip --strip-unneeded {} \; 2>/dev/null || true && \
    # Remove static libs
    find /tmp/out -name "*.a" -delete

# ---------------------------------------------------
# Stage 2: Final Runtime
FROM gcr.io/distroless/cc:latest

# Copy the staging area
COPY --from=builder /tmp/out/usr /usr
COPY --from=builder /tmp/out/lib /lib

# Add busybox for shell support
COPY --from=busybox:latest /bin/busybox /bin/sh
COPY --from=busybox:latest /bin/busybox /bin/busybox

WORKDIR /app

# Lua environment variables
ENV LUA_PATH="/usr/local/share/lua/5.1/?.lua;/usr/local/share/lua/5.1/?/init.lua;./?.lua;;"
ENV LUA_CPATH="/usr/local/lib/lua/5.1/?.so;./?.so;;"

# Point to your actual script
ENTRYPOINT ["/usr/local/bin/luajit", "main.lua"]