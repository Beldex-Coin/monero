
set(TRANSLATION_FILES "")
foreach(qm_file ${qm_files})
    file(READ "${qm_file}" trans_data HEX)
    file(RELATIVE_PATH basename "${base_dir}" "${qm_file}")
    string(REGEX REPLACE "([0-9a-f][0-9a-f])" "\\\\x\\1" trans_data "${trans_data}")
    set(TRANSLATION_FILES "${TRANSLATION_FILES}  {\"${basename}\"s, \"${trans_data}\"s},\n")
endforeach()

configure_file(${in_file} ${out_file} @ONLY)
