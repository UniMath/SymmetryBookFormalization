#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

import json
import re
import sys
import time
from utils import eprint

CONCEPT_REGEX = re.compile(
    r'\{\{#concept "([^"]+)"(.*?)\}\}')

WIKIDATA_ID_REGEX = re.compile(
    r'WDID=(\S+)')

WIKIDATA_LABEL_REGEX = re.compile(
    r'WD="([^"]+)"')

AGDA_REGEX = re.compile(
    r'Agda=(\S+)')

LINK_REGEX = re.compile(
    r'\[(.*?)\]\(.*\)')

EXTERNAL_LINKS_REGEX = re.compile(
    r'## External links\s+', re.MULTILINE)


def make_definition_regex(definition):
    return re.compile(
        r'<a id="(\d+)" href="[^"]+" class="[^"]+">' + definition + r'</a>')


def does_support(backend):
    return backend == 'html'


def match_wikidata_id(meta_text):
    m = WIKIDATA_ID_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def match_wikidata_label(meta_text):
    m = WIKIDATA_LABEL_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def match_agda_name(meta_text):
    m = AGDA_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def get_definition_id(name, content):
    definition_regex = make_definition_regex(name)
    m = definition_regex.search(content)
    if m is None:
        return None

    return m.group(1)


def sup_link_reference(href, content, brackets=True, new_tab=False):
    # f-strings can't contain backslashes, so we can't escape the quotes
    link_target = new_tab * ' target="_blank"'
    return f'<sup>{brackets * "["}<a href="{href}"{link_target}>{content}</a>{brackets * "]"}</sup>'


def sub_match_for_concept(m, mut_index, config, path, initial_content):
    text = m.group(1)
    metadata = m.group(2)
    wikidata_id = match_wikidata_id(metadata)
    wikidata_label = match_wikidata_label(metadata)
    agda_name = match_agda_name(metadata)
    plaintext = LINK_REGEX.sub(r'\1', text)
    url_path = path[:-2] + 'html'
    index_entry = {
        'name': plaintext,
        'text': text
    }
    anchor = ''
    target = ''
    target_id = None
    references = []
    if wikidata_id is not None and wikidata_id != 'NA':
        index_entry['wikidata'] = wikidata_id
        index_entry['link'] = f'{url_path}#{wikidata_id}'
        target_id = wikidata_id
        anchor += f'<a id="{target_id}" class="wikidata"><span style="display:none">{plaintext}</span></a>'
        references.append(sup_link_reference(config.get(
            'mage-template').format(wikidata_id=wikidata_id), 'WD', True, True))
    if agda_name is not None:
        target_id = f'concept-{agda_name}'
        anchor += f'<a id="{target_id}" class="concept"></a>'
        agda_id = get_definition_id(agda_name, initial_content)
        if agda_id is not None:
            destination = f'{url_path}#{agda_id}'
            index_entry['definition'] = destination
            references.append(sup_link_reference(destination, 'AG'))
        else:
            eprint('Concept definition not found:', plaintext,
                   '; expected', agda_name, 'to exist in', path)
    if target_id is not None:
        references.append(f'<sup><a href="#{target_id}"></a></sup>')
        references.append(sup_link_reference(f'#{target_id}', '¶', False))
    if wikidata_label is not None:
        index_entry['__wikidata_label'] = wikidata_label
    mut_index.append(index_entry)
    return f'{anchor}<b>{text}</b>{"".join(reversed(references))}'


def tag_concepts_chapter_rec_mut(chapter, config, mut_index):
    mut_local_index = []
    chapter['content'] = CONCEPT_REGEX.sub(
        lambda m: sub_match_for_concept(
            m, mut_local_index, config, chapter['path'], chapter['content']),
        chapter['content'])
    external_references = []
    for entry in mut_local_index:
        wikidata_label = entry.pop('__wikidata_label', None)
        wikidata_id = entry.get('wikidata', None)
        if wikidata_label is not None and wikidata_id is not None:
            mage_link = config.get(
                'mage-template').format(wikidata_id=wikidata_id)
            external_references.append(
                f'<a href="{mage_link}">{wikidata_label}</a> at MaGE')
            wikidata_link = config.get(
                'wikidata-template').format(wikidata_id=wikidata_id)
            external_references.append(
                f'<a href="{wikidata_link}">{wikidata_label}</a> at Wikidata')
            pass
        mut_index.append(entry)
    if external_references != []:
        formatted_references = ''.join(
            map(lambda a: f'- {a}\n', external_references))
        external_links_location = EXTERNAL_LINKS_REGEX.search(
            chapter['content'])
        if external_links_location is not None:
            insert_at = external_links_location.end()
            chapter['content'] = chapter['content'][:insert_at] + \
                formatted_references + chapter['content'][insert_at:]
        else:
            chapter['content'] += f'\n## External links\n\n{formatted_references}'
    tag_concepts_sections_rec_mut(chapter['sub_items'], config, mut_index)


def tag_concepts_sections_rec_mut(sections, config, mut_index):
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        tag_concepts_chapter_rec_mut(chapter, config, mut_index)


def tag_concepts_root_section(section, config, mut_index):
    chapter = section.get('Chapter')
    if chapter is not None:
        tag_concepts_chapter_rec_mut(chapter, config, mut_index)

    return section


if __name__ == '__main__':
    if len(sys.argv) > 1:
        arguments = sys.argv[1:]
        # Indicate with the exit code whether the preprocessor supports the
        # given backend or not
        if arguments[0] == 'supports':
            if not does_support(arguments[1]):
                sys.exit(1)
            else:
                sys.exit(0)

    # Load the book contents from standard input
    context, book = json.load(sys.stdin)
    concepts_config = context['config']['preprocessor']['concepts']

    # Thread the index through execution
    mut_index = []
    start = time.time()
    if bool(concepts_config.get('enable', True)) == True:
        book['sections'] = list(map(
            lambda s: tag_concepts_root_section(s, concepts_config, mut_index),
            book['sections']))
    else:
        eprint('Skipping concept tagging, enable option was',
               concepts_config.get('enable'))

    end = time.time()
    eprint(end - start)

    if mut_index != []:
        with open(concepts_config.get('output-file', 'concept_index.json'), 'w') as index_f:
            json.dump(mut_index, index_f)

    # Pass the book back to mdbook
    json.dump(book, sys.stdout)
