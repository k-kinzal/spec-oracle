/** @type {import('next').NextConfig} */
const nextConfig = {
  // The gRPC BFF (lib/grpc.ts) reads the .proto off disk and talks HTTP/2 to
  // specd; those packages must run as ordinary Node requires, not be bundled by
  // webpack (bundling breaks proto-loader's dynamic file read and grpc-js's
  // native-ish internals). Keeping them external is the Next 14 way to do that.
  experimental: {
    serverComponentsExternalPackages: ["@grpc/grpc-js", "@grpc/proto-loader"],
  },
  // Cosmograph ships as ESM; transpiling it (and its cosmos core) keeps the Next
  // build happy across module formats.
  transpilePackages: ["@cosmograph/react", "@cosmograph/cosmos"],
};

export default nextConfig;
