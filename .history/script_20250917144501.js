document.addEventListener("DOMContentLoaded", () => {
  // --- Main Setup & Event Listeners ---
  const solveBtn = document.getElementById("solve-btn");
  const autoSolveCheck = document.getElementById("auto-solve-check");
  const inputs = [
    document.getElementById("term-input"),
    document.getElementById("dont-care-input"),
    document.getElementById("variable-select"),
    document.getElementById("term-type-select"),
  ];

  if (solveBtn) {
    solveBtn.addEventListener("click", solveKmap);
  }

  inputs.forEach((input) => {
    if (input) {
      input.addEventListener("input", () => {
        if (autoSolveCheck && autoSolveCheck.checked) {
          debouncedSolve();
        }
      });
    }
  });

  let debounceTimer;
  const debouncedSolve = () => {
    clearTimeout(debounceTimer);
    debounceTimer = setTimeout(solveKmap, 300);
  };

  // --- Core Solver Logic ---
  function solveKmap() {
    const solutionDiv = document.getElementById("solution");
    const errorDiv = document.getElementById("error-message");
    if (!solutionDiv || !errorDiv) return;

    solutionDiv.innerHTML = "";
    errorDiv.innerHTML = "";

    try {
      const { requiredTerms, dontCares, numVars, termType } =
        parseAndValidateInputs();
      
      const requiredSet = new Set(requiredTerms);
      const dontCareSet = new Set(dontCares);

      let termsToGroup, termsToCover;

      if (termType === "min") {
        // SoP: Group 1s and Xs
        termsToGroup = [...new Set([...requiredTerms, ...dontCares])];
        // But only need to cover the 1s
        termsToCover = requiredTerms;
      } else {
        // PoS: Group 0s and Xs
        const maxTerm = Math.pow(2, numVars) - 1;
        const allTerms = Array.from({ length: maxTerm + 1 }, (_, i) => i);
        const maxTermSet = new Set(requiredTerms);
        const zeroTerms = allTerms.filter(
          (t) => !maxTermSet.has(t) && !dontCareSet.has(t)
        );
        termsToGroup = [...new Set([...zeroTerms, ...dontCares])];
        termsToCover = zeroTerms;
      }

      const primeImplicants = findPrimeImplicants(termsToGroup, numVars);
      const essentialGroups = selectEssentialImplicants(
        primeImplicants,
        termsToCover
      );
      const simplifyFn = termType === "min" ? simplifyGroupSoP : simplifyGroupPoS;
      const simplifiedTerms = essentialGroups.map((group) =>
        simplifyFn(group, numVars)
      );

      // Render all steps
      renderSolution(
        requiredTerms,
        dontCares,
        requiredSet,
        dontCareSet,
        numVars,
        essentialGroups,
        simplifiedTerms,
        termType
      );
    } catch (error) {
      errorDiv.innerText = error.message;
    }
  }

  function parseAndValidateInputs() {
    const requiredStr = document.getElementById("term-input").value;
    const dontCareStr = document.getElementById("dont-care-input").value;
    const numVars = parseInt(document.getElementById("variable-select").value);
    const termType = document.getElementById("term-type-select").value;

    const parse = (str) =>
      str
        .split(/[\s,]+/)
        .filter((s) => s.trim() !== "")
        .map(Number);

    const requiredTerms = parse(requiredStr);
    const dontCares = parse(dontCareStr);

    if (requiredTerms.some(isNaN) || dontCares.some(isNaN)) {
      throw new Error("Input contains non-numeric values.");
    }

    const maxTerm = Math.pow(2, numVars) - 1;
    const allTermsInput = [...requiredTerms, ...dontCares];

    if (allTermsInput.some((t) => t > maxTerm)) {
      throw new Error(
        `Terms cannot be greater than ${maxTerm} for ${numVars} variables.`
      );
    }

    // Check for overlap
    const requiredSet = new Set(requiredTerms);
    const overlap = dontCares.some(d => requiredSet.has(d));
    if (overlap && requiredTerms.length > 0 && dontCares.length > 0) {
         throw new Error("The same term cannot be in both required and don't care lists.");
    }

    return {
      requiredTerms: [...requiredSet].sort((a, b) => a - b),
      dontCares: [...new Set(dontCares)].sort((a, b) => a - b),
      numVars,
      termType,
    };
  }

  // --- Quine-McCluskey Logic (No changes needed) ---
  function findPrimeImplicants(terms, numVars) {
    if (terms.length === 0) return [];
    let groups = terms.map((m) => [m]);
    const primeImplicants = [];
    while (groups.length > 0) {
      const usedInNextLevel = new Set();
      const nextGroupsMap = new Map();
      let madeCombination = false;
      for (let i = 0; i < groups.length; i++) {
        for (let j = i + 1; j < groups.length; j++) {
          const g1 = groups[i],
            g2 = groups[j];
          if (g1.length !== g2.length) continue;
          const diff = g1.map((val, idx) => val ^ g2[idx]);
          const firstDiff = diff[0];
          const isPowerOfTwo =
            firstDiff > 0 && (firstDiff & (firstDiff - 1)) === 0;
          if (diff.every((d) => d === firstDiff) && isPowerOfTwo) {
            madeCombination = true;
            usedInNextLevel.add(JSON.stringify(g1));
            usedInNextLevel.add(JSON.stringify(g2));
            const combined = [...new Set([...g1, ...g2])].sort((a, b) => a - b);
            nextGroupsMap.set(JSON.stringify(combined), combined);
          }
        }
      }
      groups.forEach((g) => {
        if (!usedInNextLevel.has(JSON.stringify(g))) primeImplicants.push(g);
      });
      if (!madeCombination) break;
      groups = Array.from(nextGroupsMap.values());
    }
    return Array.from(new Set(primeImplicants.map(JSON.stringify)), JSON.parse);
  }

  function selectEssentialImplicants(primeImplicants, termsToCover) {
     if (termsToCover.length === 0) {
        // If there are no required terms (e.g., all don't cares or empty input), the function is 0 (for SoP) or 1 (for PoS).
        return []; 
     }
    const coverage = new Map(termsToCover.map((m) => [m, []]));
    primeImplicants.forEach((group, i) => {
      group.forEach((m) => {
        if (coverage.has(m)) coverage.get(m).push(i);
      });
    });
    const essentialPIIndices = new Set();
    const coveredTerms = new Set();
    coverage.forEach((piIndices, term) => {
      if (piIndices.length === 1) {
        const piIndex = piIndices[0];
        essentialPIIndices.add(piIndex);
        primeImplicants[piIndex].forEach((t) => {
          if (termsToCover.includes(t)) coveredTerms.add(t);
        });
      }
    });
    let essentialGroups = Array.from(essentialPIIndices).map(
      (i) => primeImplicants[i]
    );
    let uncoveredTerms = termsToCover.filter((t) => !coveredTerms.has(t));
    let remainingPIs = primeImplicants.filter(
      (_, i) => !essentialPIIndices.has(i)
    );
    while (uncoveredTerms.length > 0) {
      if (remainingPIs.length === 0) break;
      remainingPIs.sort((a, b) => {
        const coverA = a.filter((t) => uncoveredTerms.includes(t)).length;
        const coverB = b.filter((t) => uncoveredTerms.includes(t)).length;
        return coverB - coverA || a.length - b.length;
      });
      const bestPI = remainingPIs.shift();
      if (bestPI && bestPI.some(t => uncoveredTerms.includes(t))) { // Only add if it covers something new
        essentialGroups.push(bestPI);
        bestPI.forEach((t) => {
          const index = uncoveredTerms.indexOf(t);
          if (index > -1) uncoveredTerms.splice(index, 1);
        });
      } else if (!bestPI) {
          break; // No more PIs left
      }
    }
    return essentialGroups;
  }

  function decToBin(dec, len) {
    return (dec >>> 0).toString(2).padStart(len, "0");
  }

  function simplifyGroupSoP(group, numVars) {
    if (group.length === 0) return "";
    if (group.length === Math.pow(2, numVars)) return "1";
    const variables = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(0, numVars);
    const binaryReps = group.map((m) => decToBin(m, numVars));
    let term = "";
    for (let i = 0; i < numVars; i++) {
      const firstBit = binaryReps[0][i];
      if (binaryReps.every((bin) => bin[i] === firstBit)) {
        term += variables[i];
        if (firstBit === "0") term += "'";
      }
    }
    return term;
  }

  function simplifyGroupPoS(group, numVars) {
    if (group.length === 0) return "";
    if (group.length === Math.pow(2, numVars)) return "0";
    const variables = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(0, numVars);
    const binaryReps = group.map((m) => decToBin(m, numVars));
    let term = [];
    for (let i = 0; i < numVars; i++) {
      const firstBit = binaryReps[0][i];
      if (binaryReps.every((bin) => bin[i] === firstBit)) {
        let literal = variables[i];
        if (firstBit === "1") literal += "'";
        term.push(literal);
      }
    }
    return `(${term.join(" + ")})`;
  }

  // --- NEW: Truth Table Generation ---
  function generateTruthTableHTML(requiredSet, dontCareSet, numVars) {
    const variables = "ABCDE".slice(0, numVars).split("");
    let header = variables.map((v) => `<th>${v}</th>`).join("");
    header += "<th>Output (F)</th>";
    let rows = "";
    const numRows = Math.pow(2, numVars);

    for (let i = 0; i < numRows; i++) {
      const bin = decToBin(i, numVars);
      let output;
      let outputClass = "";
      if (requiredSet.has(i)) {
        output = "1";
        outputClass = "out-one";
      } else if (dontCareSet.has(i)) {
        output = "X";
        outputClass = "dont-care";
      } else {
        output = "0";
        outputClass = "out-zero";
      }
      const inputs = bin.split("").map((b) => `<td>${b}</td>`).join("");
      rows += `<tr><td class="minterm-index">${i}</td>${inputs}<td class="${outputClass}">${output}</td></tr>`;
    }
     // Add minterm index col header
     header = `<th>Row</th>` + header;

    return `<table class="truth-table"><thead><tr>${header}</tr></thead><tbody>${rows}</tbody></table>`;
  }

  // --- NEW: Standard Form Generation ---
  function generateStandardFormsHTML(requiredTerms, dontCares, numVars, termType) {
    const maxTerm = Math.pow(2, numVars) - 1;
    const allTerms = new Set(Array.from({ length: maxTerm + 1 }, (_, i) => i));
    const dontCareSet = new Set(dontCares);
    const requiredSet = new Set(requiredTerms);

    let sopTerms, posTerms;

    if (termType === "min") {
      // Input was Minterms (SoP)
      sopTerms = requiredTerms;
      posTerms = [...allTerms].filter(
        (t) => !requiredSet.has(t) && !dontCareSet.has(t)
      );
    } else {
      // Input was Maxterms (PoS)
      posTerms = requiredTerms;
      sopTerms = [...allTerms].filter(
        (t) => !requiredSet.has(t) && !dontCareSet.has(t)
      );
    }

    return `
        <div class="std-form"><strong>Standard SoP:</strong> F = &Sigma;m(${sopTerms.join(", ")})</div>
        <div class="std-form"><strong>Standard PoS:</strong> F = &Pi;M(${posTerms.join(", ")})</div>
      `;
  }
  
  // --- NEW: Logic Diagram Description ---
    function generateLogicDiagramsHTML(simplifiedTerms, numVars, termType) {
        if (simplifiedTerms.length === 0 || (simplifiedTerms.length === 1 && (simplifiedTerms[0] === '0' || simplifiedTerms[0] === '1'))) {
             if (simplifiedTerms[0] === '1') return "<p>Circuit is trivial: F is connected directly to <strong>VCC (Logic 1)</strong>.</p>";
             if (simplifiedTerms[0] === '0') return "<p>Circuit is trivial: F is connected directly to <strong>GND (Logic 0)</strong>.</p>";
             // Handle empty input case
             return (termType === 'min') ? "<p>Circuit output is constant <strong>0 (GND)</strong>.</p>" : "<p>Circuit output is constant <strong>1 (VCC)</strong>.</p>";
        }

        const variables = "ABCDE".slice(0, numVars).split('');
        const inputs = variables.join(", ");
        let basicHtml = '', universalHtml = '';

        if (termType === 'min') { // SoP
            const termsStr = simplifiedTerms.map(t => `<strong>${t}</strong>`).join(", ");
            const orInputCount = simplifiedTerms.length;
            basicHtml = `
                <h4>Basic Gates Implementation (AND-OR Logic):</h4>
                <ol>
                    <li><strong>Inputs:</strong> ${inputs} (and their NOT gate inversions as needed).</li>
                    <li>Create <strong>${orInputCount} AND gate(s)</strong>, one for each product term: ${termsStr}.</li>
                    <li>Connect the outputs of all these AND gates to the inputs of a single <strong>${orInputCount}-input OR gate</strong>.</li>
                    <li>The output of this final OR gate is F.</li>
                </ol>`;
            universalHtml = `
                <h4>Universal Gates Implementation (NAND-NAND Logic):</h4>
                <ol>
                    <li><strong>Inputs:</strong> ${inputs}. Create inverted inputs (A', B', etc.) using NAND gates (tie inputs together).</li>
                    <li>Implement each product term (e.g., AB'C) using a <strong>NAND gate</strong> (Inputs: A, B', C).</li>
                    <li>This creates ${orInputCount} NAND gates (one for each term).</li>
                    <li>Connect the outputs of all these 'term' NAND gates to the inputs of one <strong>final NAND gate</strong>.</li>
                    <li>This NAND-NAND implementation is equivalent to the SoP expression.</li>
                </ol>`;
        } else { // PoS
            const termsStr = simplifiedTerms.map(t => `<strong>${t}</strong>`).join("");
             const andInputCount = simplifiedTerms.length;
            basicHtml = `
                <h4>Basic Gates Implementation (OR-AND Logic):</h4>
                <ol>
                    <li><strong>Inputs:</strong> ${inputs} (and their NOT gate inversions as needed).</li>
                    <li>Create <strong>${andInputCount} OR gate(s)</strong>, one for each sum term: ${termsStr}.</li>
                    <li>Connect the outputs of all these OR gates to the inputs of a single <strong>${andInputCount}-input AND gate</strong>.</li>
                    <li>The output of this final AND gate is F.</li>
                </ol>`;
             universalHtml = `
                <h4>Universal Gates Implementation (NOR-NOR Logic):</h4>
                <ol>
                    <li><strong>Inputs:</strong> ${inputs}. Create inverted inputs (A', B', etc.) using NOR gates (tie inputs together).</li>
                    <li>Implement each sum term (e.g., (A+B'+C)) using a <strong>NOR gate</strong> (Inputs: A, B', C).</li>
                    <li>This creates ${andInputCount} NOR gates (one for each term).</li>
                    <li>Connect the outputs of all these 'term' NOR gates to the inputs of one <strong>final NOR gate</strong>.</li>
                    <li>This NOR-NOR implementation is equivalent to the PoS expression.</li>
                </ol>`;
        }
        return `<div class="circuit-logic">${basicHtml}${universalHtml}</div>`;
    }

  // --- UPDATED: Rendering Logic ---
  function renderSolution(
    requiredTerms,
    dontCares,
    requiredSet,
    dontCareSet,
    numVars,
    groups,
    terms,
    termType
  ) {
    const solutionDiv = document.getElementById("solution");
    const colors = [
      "#f87171", "#fb923c", "#fbbf24", "#a3e635", "#4ade80",
      "#34d399", "#22d3ee", "#60a5fa", "#818cf8", "#a78bfa",
      "#f472b6", "#fb7185",
    ];
    
    const operator = termType === "min" ? " + " : "";
    let finalExpression = terms.join(operator) || (termType === 'min' ? '0' : '1');

    let finalHtml = "";

    // --- Step 1: Truth Table ---
    finalHtml += `
      <div class="solution-step">
        <h2>Step 1: Truth Table</h2>
        ${generateTruthTableHTML(requiredSet, dontCareSet, numVars)}
      </div>`;

    // --- Step 2: Standard Forms ---
    finalHtml += `
      <div class="solution-step">
        <h2>Step 2: Standard Canonical Forms</h2>
        ${generateStandardFormsHTML(requiredTerms, dontCares, numVars, termType)}
      </div>`;
    
    // --- Step 3 & 4: K-Map & Final Expression (Combined) ---
    finalHtml += `
       <div class="solution-step">
         <h2>Step 3 & 4: K-Map Minimization & Final Expression</h2>
         <div class="final-expression">F = ${finalExpression}</div>
         <p>This expression is derived algorithmically (using the Quine-McCluskey method, which is equivalent to K-Map grouping) to find the minimal ${termType === 'min' ? 'SoP' : 'PoS'} form.</p>
       </div>`;

    // --- K-Map Visual ---
    finalHtml += `
      <div class="solution-step">
        <h2>Complete K-Map with Groupings</h2>
        ${renderKMap(requiredTerms, dontCares, numVars, groups, colors)}
      </div>`;

    // --- Step 5: Logic Circuits ---
    finalHtml += `
       <div class="solution-step">
         <h2>Step 5: Logic Circuit Implementation</h2>
         ${generateLogicDiagramsHTML(terms, numVars, termType)}
       </div>`;

    // --- K-Map Group Steps ---
    groups.forEach((group, index) => {
      finalHtml += `
        <div class="solution-step group-step">
            <h2>Grouping Detail ${index + 1}: (${group.join(",")})</h2>
            <p class="final-expression" style="border-color:${colors[index % colors.length]}; color:${colors[index % colors.length]};">Term: ${terms[index]}</p>
            ${renderKMap(
              requiredTerms,
              dontCares,
              numVars,
              [group],
              [colors[index % colors.length]]
            )}
        </div>`;
    });

    solutionDiv.innerHTML = finalHtml;
  }

  // --- K-Map Layout/Render (No changes needed) ---
  function getKMapLayout(numVars) {
    if (numVars <= 2) { // Default to 2-var for 1 or 2
      const rowVars = ["A"],
        colVars = ["B"];
      const rows = ["0", "1"],
        cols = ["0", "1"];
      const getMinterm = (mapIdx, r, c) => parseInt(rows[r] + cols[c], 2);
      return { rowVars, colVars, rows, cols, getMinterm, mapCount: 1 };
    }
    if (numVars === 3) {
      const rowVars = ["A"],
        colVars = ["B", "C"];
      const rows = ["0", "1"],
        cols = ["00", "01", "11", "10"];
      const getMinterm = (mapIdx, r, c) => parseInt(rows[r] + cols[c], 2);
      return { rowVars, colVars, rows, cols, getMinterm, mapCount: 1 };
    }
    if (numVars === 4) {
      const rowVars = ["A", "B"],
        colVars = ["C", "D"];
      const rows = ["00", "01", "11", "10"],
        cols = ["00", "01", "11", "10"];
      const getMinterm = (mapIdx, r, c) => parseInt(rows[r] + cols[c], 2);
      return { rowVars, colVars, rows, cols, getMinterm, mapCount: 1 };
    }
    if (numVars === 5) {
      const rowVars = ["B", "C"],
        colVars = ["D", "E"];
      const rows = ["00", "01", "11", "10"],
        cols = ["00", "01", "11", "10"];
      const getMinterm = (mapIdx, r, c) =>
        parseInt(mapIdx.toString() + rows[r] + cols[c], 2);
      return { rowVars, colVars, rows, cols, getMinterm, mapCount: 2 };
    }
  }

  function renderKMap(
    requiredTerms,
    dontCares,
    numVars,
    groupsToHighlight = [],
    colors = []
  ) {
    const layout = getKMapLayout(numVars);
    const requiredSet = new Set(requiredTerms);
    const dontCareSet = new Set(dontCares);
    let html = '<div class="kmap-container">';
    for (let mapIdx = 0; mapIdx < layout.mapCount; mapIdx++) {
      if (layout.mapCount > 1)
        html += `<div><h3>${numVars === 5 ? "A" : "V"}=${mapIdx}</h3>`;
      html += '<table class="kmap-table">';
      html += `<tr><th>${layout.rowVars.join("")}\\${layout.colVars.join(
        ""
      )}</th>`;
      layout.cols.forEach((c) => (html += `<th>${c}</th>`));
      html += "</tr>";
      layout.rows.forEach((r, rIdx) => {
        html += `<tr><th>${r}</th>`;
        layout.cols.forEach((c, cIdx) => {
          const minterm = layout.getMinterm(mapIdx, rIdx, cIdx);
          let val = "0";
          let valClass = "";
          if (requiredSet.has(minterm)) {
            val = "1";
          } else if (dontCareSet.has(minterm)) {
            val = "X";
            valClass = "dont-care";
          }
          let styles = "";
          groupsToHighlight.forEach((group, gIdx) => {
            if (group.includes(minterm)) {
              styles += `border: 3px solid ${
                colors[gIdx % colors.length]
              }; box-shadow: 0 0 10px ${colors[gIdx % colors.length]};`;
            }
          });
          html += `<td style="${styles}">
                                 <span class="minterm-index">${minterm}</span>
                                 <span class="${valClass}">${val}</span>
                               </td>`;
        });
        html += "</tr>";
      });
      html += "</table>";
      if (layout.mapCount > 1) html += `</div>`;
    }
    html += "</div>";
    return html;
  }
});