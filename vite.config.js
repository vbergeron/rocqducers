import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import path from "path";

export default defineConfig({
  plugins: [react()],
  resolve: {
    alias: {
      "@rocqducers": path.resolve(
        __dirname,
        "rocqducers/_build/default/emit/output"
      ),
      "melange.js": path.resolve(
        __dirname,
        "rocqducers/_build/default/emit/output/node_modules/melange.js"
      ),
      "melange": path.resolve(
        __dirname,
        "rocqducers/_build/default/emit/output/node_modules/melange"
      ),
    },
  },
});
