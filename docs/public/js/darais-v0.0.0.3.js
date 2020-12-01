/////////////////////
// Added Eelements //
/////////////////////

// Nav //

$('body').prepend($(
    " <nav class='navbar navbar-expand-md navbar-dark bg-dark mb-4'> "
  + "   <div class='container'>                                      "
  + "     <a id='nav-title' class='navbar-brand' href='#'>           "
  + "     </a>                                                       "
  + "   </div>                                                       "
  + " </nav>                                                         "
  ));

// Timestamp //

$('main').append($(
  " <div id='timestamp'></div> "
));

//////////////
// Showdown //
//////////////

var sdown = new showdown.Converter();
sdown.setOption('tables', true);
sdown.setOption('disableForced4SpacesIndentedSublists', true);
$("pre.markdown").each(function () {
  var e = $("<div class=markdown></div>");
  e.html(sdown.makeHtml($(this).text()).replace(/\u22D6/g,"&lt;").replace(/\u22D7/g,"&gt;"));
  $.each(this.attributes,function(i,a) {
    e.attr(a.name,a.value);
  });
  $(this).replaceWith(e);
});

///////////
// Title //
///////////

function setTitle(title) {
  $(document).attr('title',title);
  $("#nav-title").text(title);
};

var title = "!!!TITLE!!!"

// Look for a title meta tag in head
title = $('meta[name=title]').attr('content');

// Look for link to #title
$("a[href='#title']").each(function (i,e) {
  title = $(e).text();
  $(e).remove();
});

setTitle(title);

///////////////
// Timestamp //
///////////////

$("#timestamp")
  .addClass("text-right")
  .addClass("text-secondary")
  .append($("<em>Last updated: " + new Date(document.lastModified).toLocaleDateString() + "</em>"));

/////////////
// Styling //
/////////////

$('main')
  .addClass('container')
  .addClass('text-justify');

$("table:not(.raw)").each(function () {
  $(this).addClass("table table-striped table-borderless table-sm");
});

$("thead").each(function () {
  $(this).addClass("thead-dark");
});
