# github-core-clone-01 forge

A standalone GitHub-compatible git forge: one Node 22 process (standard library
only) serving git smart HTTP (upload-pack v2/v0, receive-pack v0), the REST v3
API, GraphQL v4 and MCP from its own in-memory store. No UI, no git binary, no
outside service.

## Run it

```sh
node --experimental-strip-types main.ts
```

With `MAKEFUN_ENV_URL` set it binds an ephemeral port, registers with the
suite and exits when the suite says done. Without it (local development) it
serves on `$PORT` (default 8765) until stopped. Auth is `Authorization:
Bearer $MAKEFUN_SHOP_TOKEN`.

## Layout

- `main.ts`: the entry <-> env lifecycle.
- `app.ts`: the whole server (git packfile/pkt-line implementation, REST,
  GraphQL, MCP).
- `package.json`, `tsconfig.json`, `LICENSE` (MIT).
