// Search box for the one-page web paper: type a word, and only the sections
// (and appendices) that contain it stay visible, with the matches marked.
// Also puts a list of contents above the box (one page has no sidebar).
// Built by plasTeX (paper/plastex.cfg, extra-js); no external libraries.
(function () {
  function init() {
    var main = document.querySelector('.main-text') || document.body;
    // plasTeX writes a section as an <h1 id=…> (a subsection as <h2 id=…>)
    // followed by its content as siblings, so a "section" here is a heading
    // plus everything up to the next one: search hides subsections one by one.
    var sections = [], cur = null;
    Array.prototype.forEach.call(main.children, function (el) {
      if ((el.tagName === 'H1' || el.tagName === 'H2') && el.id) { cur = [el]; sections.push(cur); }
      else if (cur) cur.push(el);
    });
    if (!sections.length) return;
    var box = document.createElement('input');
    box.type = 'search';
    box.placeholder = 'Search the paper';
    box.setAttribute('aria-label', 'Search the paper');
    box.style.cssText = 'width:100%;max-width:30em;font-size:1rem;padding:.4em;margin:.5em 0 1em;box-sizing:border-box';
    var info = document.createElement('div');
    info.style.cssText = 'font-size:.9rem;color:#666;margin-bottom:1em';
    var first = sections[0][0];
    var toc = document.createElement('nav');
    toc.className = 'paper-toc';
    toc.style.cssText = 'columns:16em;font-size:.95rem;margin:1em 0';
    sections.forEach(function (sec) {
      var a = document.createElement('a');
      a.href = '#' + sec[0].id;
      a.innerHTML = sec[0].innerHTML;
      a.style.cssText = 'display:block;margin:.15em 0' +
        (sec[0].tagName === 'H2' ? ';padding-left:1.2em;font-size:.9em' : '');
      toc.appendChild(a);
    });
    main.insertBefore(toc, first);
    main.insertBefore(box, first);
    main.insertBefore(info, first);
    function clearMarks() {
      Array.prototype.forEach.call(main.querySelectorAll('mark.paper-hit'), function (m) {
        m.replaceWith(document.createTextNode(m.textContent));
      });
      main.normalize();
    }
    function mark(node, q) {
      var walker = document.createTreeWalker(node, NodeFilter.SHOW_TEXT, {
        acceptNode: function (t) {
          var p = t.parentNode;
          if (p.closest('script,style,.MathJax,mjx-container')) return NodeFilter.FILTER_REJECT;
          return t.nodeValue.toLowerCase().indexOf(q) >= 0 ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;
        }
      });
      var hits = [], t;
      while ((t = walker.nextNode())) hits.push(t);
      hits.forEach(function (t) {
        var i = t.nodeValue.toLowerCase().indexOf(q);
        var rest = t.splitText(i);
        rest.splitText(q.length);
        var m = document.createElement('mark');
        m.className = 'paper-hit';
        m.textContent = rest.nodeValue;
        rest.replaceWith(m);
      });
      return hits.length;
    }
    var timer;
    box.addEventListener('input', function () {
      clearTimeout(timer);
      timer = setTimeout(function () {
        clearMarks();
        var q = box.value.trim().toLowerCase();
        var shown = 0, total = 0;
        sections.forEach(function (s) {
          var n = 0;
          s.forEach(function (el) { n += q ? mark(el, q) : 1; });
          s.forEach(function (el) { el.style.display = n ? '' : 'none'; });
          if (n) { shown++; total += n; }
        });
        info.textContent = q ? (total ? total + ' matches in ' + shown + ' sections' : 'No matches') : '';
      }, 200);
    });
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
