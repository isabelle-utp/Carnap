/**
 * Carnap Answers Downloader
 * Scrapes top-level exercise answers from the DOM and downloads them as a formatted text file.
 */
function downloadCarnapAnswers() {
  const records = [];

  // Extract document title for header; fall back to document.title if no heading element exists
  const titleElement = document.querySelector('h1, .carnap-title, #title, header h1');
  const sheetTitle = titleElement ? titleElement.innerText.trim() : document.title;

  // Query top-level exercise nodes and exclude nested elements to avoid duplicate scraping
  const allNodes = Array.from(document.querySelectorAll('.exercise, [data-carnap-type]'));
  const topLevelNodes = allNodes.filter(node => {
    return !allNodes.some(otherNode => otherNode !== node && otherNode.contains(node));
  });

  // Iterate over each top-level exercise to extract answers
  topLevelNodes.forEach((node, index) => {
    // Derive exercise identifier from data attributes, element id, or fallback index
    const id = node.getAttribute('data-carnap-label') || node.id.replace(/^exercise-/, '') || `Exercise_${index + 1}`;
    let answers = [];

    // 1. Extract answers from CodeMirror instances (used for proofs, syntax checkers, and translations)
    const cmNodes = node.querySelectorAll('.CodeMirror');
    cmNodes.forEach(cmNode => {
      if (cmNode.CodeMirror) {
        const val = cmNode.CodeMirror.getValue().trim();
        if (val && !answers.includes(val)) answers.push(val);
      }
    });

    // 2. Extract standard inputs, multiple-choice radio buttons, checkboxes, and select dropdowns
    if (answers.length === 0) {
      const inputs = node.querySelectorAll('input:not([type="hidden"]), textarea, select');
      inputs.forEach(input => {
        // Skip table inputs (handled separately in Truth Tables section)
        if (input.closest('table')) return;

        if (input.tagName.toLowerCase() === 'select') {
          // Extract selected option text or value from dropdown
          const opt = input.options[input.selectedIndex];
          if (opt && opt.value.trim() !== '') {
            const val = opt.text.trim() || opt.value.trim();
            if (val && !answers.includes(val)) answers.push(val);
          }
        } else if (input.type === 'radio' || input.type === 'checkbox') {
          // Extract text for checked radio button or checkbox
          if (input.checked) {
            let labelText = '';
            
            // Check for associated <label for="..."> element
            if (input.id) {
              const lbl = node.querySelector(`label[for="${CSS.escape(input.id)}"]`);
              if (lbl) labelText = lbl.innerText.trim();
            }
            
            // Fall back to parent <label> if no explicit 'for' attribute is bound
            if (!labelText) {
              const parentLbl = input.closest('label');
              if (parentLbl) labelText = parentLbl.innerText.trim();
            }
            
            const finalVal = labelText || input.value.trim() || '[Selected]';
            if (finalVal && !answers.includes(finalVal)) answers.push(finalVal);
          }
        } else if (input.value.trim() !== '') {
          // Standard text inputs and textareas
          answers.push(input.value.trim());
        }
      });
    }

    // 3. Extract Truth Tables row by row
    const tables = node.querySelectorAll('table');
    tables.forEach(table => {
      const tableRows = [];
      table.querySelectorAll('tr').forEach(row => {
        const rowCells = [];
        row.querySelectorAll('th, td').forEach(cell => {
          const cellInput = cell.querySelector('input, select');
          let val = cellInput ? (cellInput.value || '') : (cell.innerText || '');
          rowCells.push(val.replace(/\s+/g, ' ').trim() || '-');
        });
        if (rowCells.length > 0) tableRows.push(rowCells.join(' | '));
      });
      if (tableRows.length > 0) answers.push(tableRows.join('\n'));
    });

    // Store formatted exercise record
    records.push({
      exercise: id,
      content: answers.join('\n\n') || '[No answer provided]'
    });
  });

  // Build plain text file output content
  let outputText = `${sheetTitle.toUpperCase()}\nSaved On: ${new Date().toLocaleString()}\n----------------------------------------\n\n`;
  records.forEach(item => {
    outputText += `[${item.exercise}]\n${item.content}\n\n`;
  });

  // Prompt user for filename and trigger browser file download
  const defaultFilename = `carnap-answers-${new Date().toISOString().slice(0, 10)}.txt`;
  let fileName = prompt("Enter a filename for your answers:", defaultFilename);
  if (!fileName) return;
  if (!fileName.endsWith('.txt')) fileName += '.txt';

  const blob = new Blob([outputText], { type: 'text/plain;charset=utf-8' });
  const downloadUrl = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = downloadUrl;
  link.download = fileName;
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  URL.revokeObjectURL(downloadUrl);
}

/**
 * Carnap Answers Restorer
 * Triggers file selector, parses saved answer text file, and restores inputs in the DOM.
 */
function restoreCarnapAnswers() {
  const input = document.createElement('input');
  input.type = 'file';
  input.accept = '.txt';

  input.onchange = e => {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.readAsText(file, 'UTF-8');
    reader.onload = readerEvent => {
      parseAndRestoreCarnap(readerEvent.target.result);
    };
  };

  input.click();
}

/**
 * Main Restoration Engine
 * Maps parsed exercise answers back to Carnap DOM components and triggers native UI events.
 */
function parseAndRestoreCarnap(fileContent) {
  // Parse text content into key-value map using bracket section headers, e.g., [1.1]
  const dataMap = {};
  const sections = fileContent.split(/\n(?=\[\s*[\w\.]+\s*\])/g);

  sections.forEach(section => {
    const match = section.match(/^\[\s*([\w\.]+)\s*\]\n([\s\S]*)$/);
    if (match) {
      const label = match[1].trim();
      const content = match[2].trim();
      if (content && content !== '[No answer provided]') {
        dataMap[label] = content;
      }
    }
  });

  // Query top-level exercise nodes
  const allNodes = Array.from(document.querySelectorAll('.exercise, [data-carnap-type]'));
  const topLevelNodes = allNodes.filter(node => {
    return !allNodes.some(otherNode => otherNode !== node && otherNode.contains(node));
  });

  // Restore state for each matched exercise node
  topLevelNodes.forEach((node, index) => {
    const id = node.getAttribute('data-carnap-label') || node.id.replace(/^exercise-/, '') || `Exercise_${index + 1}`;
    const value = dataMap[id];

    if (!value) return;

    // 1. Restore Multiple Choice Options (Radio buttons & Checkboxes)
    const choiceInputs = node.querySelectorAll('input[type="radio"], input[type="checkbox"]');
    if (choiceInputs.length > 0) {
      choiceInputs.forEach(input => {
        let labelText = '';

        // Extract option label text
        if (input.id) {
          const lbl = node.querySelector(`label[for="${CSS.escape(input.id)}"]`);
          if (lbl) labelText = lbl.innerText.trim();
        }
        if (!labelText) {
          const parentLbl = input.closest('label');
          if (parentLbl) labelText = parentLbl.innerText.trim();
        }

        const inputVal = input.value.trim();

        // Match against saved answer value or label text
        const isMatch = (labelText && value.includes(labelText)) || 
                        (inputVal && inputVal !== 'on' && value.includes(inputVal));

        if (isMatch) {
          input.checked = true;
          // Dispatch DOM events so Carnap reactivity registers selection change
          input.dispatchEvent(new Event('input', { bubbles: true }));
          input.dispatchEvent(new Event('change', { bubbles: true }));
          input.dispatchEvent(new Event('click', { bubbles: true }));
        }
      });
      return;
    }

    // 2. Restore Select Dropdowns (Outside tables)
    const selects = node.querySelectorAll('select');
    if (selects.length > 0 && !node.querySelector('table')) {
      selects.forEach(select => {
        const matchingOption = Array.from(select.options).find(
          opt => value.includes(opt.text.trim()) || value.includes(opt.value.trim())
        );
        if (matchingOption) {
          select.value = matchingOption.value;
          select.dispatchEvent(new Event('input', { bubbles: true }));
          select.dispatchEvent(new Event('change', { bubbles: true }));
        }
      });
      return;
    }

    // 3. Restore Truth Tables
    const tables = node.querySelectorAll('table');
    if (tables.length > 0) {
      const savedLines = value.split('\n').map(l => l.trim()).filter(l => l.length > 0);

      tables.forEach(table => {
        const rows = Array.from(table.querySelectorAll('tr'));
        
        savedLines.forEach((line, rowIndex) => {
          if (!rows[rowIndex]) return;

          const savedCells = line.split('|').map(c => c.trim());
          const cells = Array.from(rows[rowIndex].querySelectorAll('th, td'));

          cells.forEach((cell, cellIndex) => {
            const valToRestore = savedCells[cellIndex];
            // Skip empty values or structural filler dashes
            if (!valToRestore || valToRestore === '-') return;

            // Handle Truth Table Dropdown Selects
            const select = cell.querySelector('select');
            if (select) {
              const matchingOption = Array.from(select.options).find(
                opt => opt.text.trim() === valToRestore || opt.value.trim() === valToRestore
              );
              select.value = matchingOption ? matchingOption.value : valToRestore;
              select.dispatchEvent(new Event('input', { bubbles: true }));
              select.dispatchEvent(new Event('change', { bubbles: true }));
              return;
            }

            // Handle Editable Table Inputs
            const input = cell.querySelector('input');
            if (input) {
              input.value = valToRestore;
              input.dispatchEvent(new Event('input', { bubbles: true }));
              input.dispatchEvent(new Event('change', { bubbles: true }));
              input.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', keyCode: 13, bubbles: true }));
              return;
            }

            // Handle Carnap Dynamic Click-Cycle Cells
            if (cell.classList.contains('interactive') || cell.getAttribute('data-carnap-type')) {
              if (cell.innerText.trim() !== valToRestore) {
                cell.innerText = valToRestore;
                cell.dispatchEvent(new Event('click', { bubbles: true }));
                cell.dispatchEvent(new Event('change', { bubbles: true }));
              }
            }
          });
        });
      });
      return;
    }

    // 4. Restore CodeMirror instances (Proofs, Syntax Checkers, and Translate blocks)
    const cmNodes = node.querySelectorAll('.CodeMirror');
    if (cmNodes.length > 0) {
      cmNodes.forEach(cmNode => {
        if (cmNode.CodeMirror) {
          // Set text value via CodeMirror API and refresh layout
          cmNode.CodeMirror.setValue(value);
          cmNode.CodeMirror.refresh();

          // Dispatch keyboard events on CodeMirror inner textarea to trigger Carnap evaluation engine
          const cmTextArea = cmNode.querySelector('textarea');
          if (cmTextArea) {
            cmTextArea.dispatchEvent(new Event('input', { bubbles: true }));
            cmTextArea.dispatchEvent(new Event('change', { bubbles: true }));
            cmTextArea.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', keyCode: 13, bubbles: true }));
          }
        }
      });
      return;
    }

    // 5. Fallback for standard text input elements and textareas
    const inputs = node.querySelectorAll('input:not([type="hidden"]), textarea');
    inputs.forEach(input => {
      input.value = value;
      input.dispatchEvent(new Event('input', { bubbles: true }));
      input.dispatchEvent(new Event('change', { bubbles: true }));
      input.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', keyCode: 13, bubbles: true }));
    });
  });

  alert('Answers successfully restored!');
}

/**
 * Carnap Answers Clearer
 * Resets all top-level exercise inputs in the DOM and dispatches native UI events.
 */
function clearCarnapAnswers() {
  if (!confirm("Are you sure you want to clear all answers on this page? This cannot be undone unless you have saved a backup.")) {
    return;
  }

  // Query top-level exercise nodes (matching your scraper/restorer logic)
  const allNodes = Array.from(document.querySelectorAll('.exercise, [data-carnap-type]'));
  const topLevelNodes = allNodes.filter(node => {
    return !allNodes.some(otherNode => otherNode !== node && otherNode.contains(node));
  });

  topLevelNodes.forEach(node => {
    // 1. Clear CodeMirror instances (Proofs, Syntax Checkers, Translations)
    const cmNodes = node.querySelectorAll('.CodeMirror');
    cmNodes.forEach(cmNode => {
      if (cmNode.CodeMirror) {
        cmNode.CodeMirror.setValue('');
        cmNode.CodeMirror.refresh();

        const cmTextArea = cmNode.querySelector('textarea');
        if (cmTextArea) {
          cmTextArea.dispatchEvent(new Event('input', { bubbles: true }));
          cmTextArea.dispatchEvent(new Event('change', { bubbles: true }));
        }
      }
    });

    // 2. Uncheck Radio Buttons & Checkboxes
    const choiceInputs = node.querySelectorAll('input[type="radio"], input[type="checkbox"]');
    choiceInputs.forEach(input => {
      if (input.checked) {
        input.checked = false;
        input.dispatchEvent(new Event('input', { bubbles: true }));
        input.dispatchEvent(new Event('change', { bubbles: true }));
      }
    });

    // 3. Reset Select Dropdowns (both standalone and inside truth tables)
    const selects = node.querySelectorAll('select');
    selects.forEach(select => {
      if (select.selectedIndex !== 0) {
        select.selectedIndex = 0;
        select.dispatchEvent(new Event('input', { bubbles: true }));
        select.dispatchEvent(new Event('change', { bubbles: true }));
      }
    });

    // 4. Clear Truth Table Interactive Click-Cycle Cells
    const interactiveCells = node.querySelectorAll('td.interactive, td[data-carnap-type], th.interactive, th[data-carnap-type]');
    interactiveCells.forEach(cell => {
      // Only clear cells that don't house a standard <input> or <select>
      if (!cell.querySelector('input, select') && cell.innerText.trim() !== '') {
        cell.innerText = '-'; // Carnap's default unset state for click-cycle cells
        cell.dispatchEvent(new Event('change', { bubbles: true }));
      }
    });

    // 5. Clear Standard Text Inputs & Textareas (including table text inputs)
    const textInputs = node.querySelectorAll('input:not([type="hidden"]):not([type="radio"]):not([type="checkbox"]), textarea');
    textInputs.forEach(input => {
      // Skip CodeMirror's internal hidden textarea (already handled in step 1)
      if (input.closest('.CodeMirror')) return;

      if (input.value !== '') {
        input.value = '';
        input.dispatchEvent(new Event('input', { bubbles: true }));
        input.dispatchEvent(new Event('change', { bubbles: true }));
      }
    });
  });
}