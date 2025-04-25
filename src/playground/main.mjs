const editor = CodeMirror.fromTextArea(document.getElementById("editor"), {
  lineNumbers: true,
});

editor.setSize("100%", "100%");

let mode = "full";

document.addEventListener("DOMContentLoaded", () => {
  for (const c of document.getElementById("modes").children) {
    c.children[0].addEventListener("click", (e) => setMode(e.currentTarget));
  }
});

function setMode(selectedMode) {
  mode = selectedMode.id;
  document.getElementById("mode").innerHTML = `Mode: ${selectedMode.innerHTML}`;
}

document.addEventListener("DOMContentLoaded", () => {
  for (const c of document.getElementById("examples").children) {
    c.children[0].addEventListener("click", (e) => setExample(e.currentTarget));
  }
});

function setExample(selectedExample) {
  fetch(`examples/${selectedExample.id}.f`)
    .then((res) => {
      if (!res.ok) {
        document.getElementById("result").innerHTML =
          `Error: cannot fetch ${selectedExample.id}.f`;
        return;
      }
      return res.text();
    })
    .then((exampleText) => {
      editor.doc.setValue(exampleText);
    });
}

function escapeHtml(str) {
  return str.replace(
    /[&<>'"]/g,
    (tag) =>
      ({
        "&": "&amp;",
        "<": "&lt;",
        ">": "&gt;",
        "'": "&#39;",
        '"': "&quot;",
      })[tag] || tag,
  );
}

const importObject = {
  console: {
    log: (res) => {
      document.getElementById("result").innerHTML += `${escapeHtml(res)}<br/>`;
    },
  },
};

const compileOptions = {
  builtins: ["js-string"],
  importedStringConstants: "_",
};

const { instance } = await WebAssembly.instantiateStreaming(
  fetch("interpreter.wasm"),
  importObject,
  compileOptions,
);

document.getElementById("run").addEventListener("click", () => {
  document.getElementById("result").innerHTML = "";
  instance.exports.interpret(editor.doc.getValue(), mode);
});
